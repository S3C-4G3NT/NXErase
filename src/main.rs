use anyhow::{anyhow, Context, Result};
use chrono::Local;
use clap::{ArgGroup, Parser};
use crossbeam_channel::{bounded, Sender, TrySendError};
use indicatif::{ProgressBar, ProgressStyle};
use nix::fcntl::{fallocate, FallocateFlags};
use nix::sys::statfs::statfs;
use nix::unistd::Uid;
use rand::distributions::Alphanumeric;
use rand::rngs::{OsRng, StdRng};
use rand::{Rng, RngCore, SeedableRng};
use rayon::iter::ParallelBridge;
use rayon::prelude::*;
use std::alloc::Layout;
use std::ffi::c_void;
use std::fs::{self, File, OpenOptions};
use std::io::{ErrorKind, Read, Seek, SeekFrom, Write};
use std::ops::{Deref, DerefMut};
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt};
use std::os::unix::io::AsRawFd;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;
use walkdir::WalkDir;

// Explicit imports
use ctrlc;
use num_cpus;

// --- Constants & Globals ---

static RUNNING: AtomicBool = AtomicBool::new(true);

const NFS_SUPER_MAGIC: i64 = 0x6969;
const SMB_SUPER_MAGIC: i64 = 0x517B;
const CIFS_MAGIC_NUMBER: i64 = 0xFF534D42;
const FUSE_SUPER_MAGIC: i64 = 0x65735546;
const OVERLAYFS_SUPER_MAGIC: i64 = 0x794c7630;
const FS_IMMUTABLE_FL: u64 = 0x00000010;

nix::ioctl_read!(ioctl_getflags, 'f', 1, libc::c_long);
nix::ioctl_write_ptr!(ioctl_setflags, 'f', 2, libc::c_long);

#[derive(Parser, Debug)]
#[command(name = "nxerase")]
#[command(version = "2.6.0")]
#[command(about = "Forensic-resistant secure deletion tool for NVMe and SSDs.", long_about = None)]
#[clap(group(
ArgGroup::new("mode")
.required(true)
.args(&["files", "sanitize"]),
))]
struct Cli {
    #[arg(group = "mode")]
    files: Vec<PathBuf>,

    #[arg(short = 'j', long = "jobs", default_value_t = num_cpus::get())]
    jobs: usize,

    #[arg(long = "no-progress", default_value_t = false)]
    no_progress: bool,

    #[arg(long = "dry-run", short = 'n')]
    dry_run: bool,

    #[arg(long = "verbose", short = 'v')]
    verbose: bool,

    #[arg(short = 's', long = "sanitize", group = "mode")]
    sanitize: bool,

    #[arg(long = "device")]
    device: Option<PathBuf>,

    #[arg(long = "yes")]
    yes: bool,

    #[arg(long = "allow-hardlinks")]
    allow_hardlinks: bool,

    #[arg(long = "throttle", value_name = "MS")]
    throttle_ms: Option<u64>,

    #[arg(long = "verify")]
    verify: bool,

    #[arg(long = "log-file", value_name = "PATH")]
    log_file: Option<PathBuf>,
}

// --- Safe Aligned Buffer (POSIX Implementation) ---

/// A memory buffer that uses `posix_memalign` to ensure strict 4096-byte alignment.
/// This minimizes UB risks and ensures compatibility with O_DIRECT requirements.
struct AlignedBuffer {
    ptr: NonNull<u8>,
    len: usize,
}

impl AlignedBuffer {
    fn new(size: usize) -> std::io::Result<Self> {
        if size == 0 {
            return Ok(Self {
                ptr: NonNull::dangling(),
                len: 0,
            });
        }

        let alignment = 4096;
        let mut raw_ptr: *mut c_void = std::ptr::null_mut();
        
        unsafe {
            // 1. Allocate aligned memory using POSIX standard
            let res = libc::posix_memalign(&mut raw_ptr, alignment, size);
            
            if res != 0 {
                // posix_memalign returns error code directly, not in errno
                return Err(std::io::Error::from_raw_os_error(res));
            }

            // 2. Zero the memory immediately (security + safety)
            // FIX: Cast raw_ptr (*mut c_void) to *mut u8 for write_bytes
            std::ptr::write_bytes(raw_ptr as *mut u8, 0, size);

            let ptr = NonNull::new(raw_ptr as *mut u8)
                .ok_or_else(|| std::io::Error::new(ErrorKind::Other, "posix_memalign returned null"));
            
            ptr.map(|p| Self { ptr: p, len: size })
        }
    }
}

impl Drop for AlignedBuffer {
    fn drop(&mut self) {
        if self.len > 0 {
            unsafe {
                // Must use free() because we used posix_memalign()
                libc::free(self.ptr.as_ptr() as *mut c_void);
            }
        }
    }
}

impl Deref for AlignedBuffer {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl DerefMut for AlignedBuffer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}

unsafe impl Send for AlignedBuffer {}

// --- Structs ---

struct AuditLogger {
    file: Option<Mutex<File>>,
}

impl AuditLogger {
    fn new(path: Option<PathBuf>) -> Result<Self> {
        if let Some(p) = path {
            let f = OpenOptions::new().create(true).append(true).write(true).open(p)?;
            Ok(Self { file: Some(Mutex::new(f)) })
        } else {
            Ok(Self { file: None })
        }
    }

    fn log(&self, msg: &str) {
        if let Some(mutex) = &self.file {
            if let Ok(mut f) = mutex.lock() {
                let _ = writeln!(f, "[{}] {}", Local::now().to_rfc3339(), msg);
            }
        }
    }
}

struct WipeStats {
    deleted: AtomicUsize,
    skipped: AtomicUsize,
    failed: AtomicUsize,
    verified_errors: AtomicUsize,
}

impl WipeStats {
    fn new() -> Self {
        Self {
            deleted: AtomicUsize::new(0),
            skipped: AtomicUsize::new(0),
            failed: AtomicUsize::new(0),
            verified_errors: AtomicUsize::new(0),
        }
    }
}

// --- Helper Functions ---

fn is_network_or_overlay(path: &Path) -> bool {
    if let Ok(stat) = statfs(path) {
        let magic = stat.filesystem_type().0 as i64;
        if magic == NFS_SUPER_MAGIC ||
            magic == SMB_SUPER_MAGIC ||
            magic == CIFS_MAGIC_NUMBER ||
            magic == FUSE_SUPER_MAGIC ||
            magic == OVERLAYFS_SUPER_MAGIC {
                return true;
            }
    }
    false
}

fn remove_immutable_flag(fd: i32) -> Result<()> {
    unsafe {
        let mut flags: libc::c_long = 0;
        ioctl_getflags(fd, &mut flags).context("Failed to get file flags")?;

        let imm_mask = FS_IMMUTABLE_FL as libc::c_long;
        if (flags & imm_mask) != 0 {
            flags &= !imm_mask;
            ioctl_setflags(fd, &flags).context("Failed to clear immutable flag")?;
        }
    }
    Ok(())
}

fn overwrite_file(
    file: &mut File, 
    len: u64, 
    progress_sender: Option<Sender<u64>>, 
    throttle: Option<u64>, 
    verify: bool,
    verbose: bool
) -> Result<()> {
    if len == 0 { return Ok(()); }

    let mut seed = [0u8; 32];
    OsRng.fill_bytes(&mut seed);
    let mut rng = StdRng::from_seed(seed);

    // 64KB Buffer: Fast responsive Ctrl-C, low memory usage
    let buf_size = 64 * 1024; 
    let mut buffer = AlignedBuffer::new(buf_size).context("Failed to allocate wipe buffer")?;

    let mut written: u64 = 0;
    
    // Progress Accumulation Logic
    let mut progress_accumulator: u64 = 0;
    let mut progress_alive = true; // Circuit breaker if receiver dies
    const PROGRESS_BATCH_SIZE: u64 = 64 * 1024; // Update UI every 64KB

    // --- Pass 1: Write ---
    file.seek(SeekFrom::Start(0)).context("seek to start")?;

    while written < len {
        if !RUNNING.load(Ordering::SeqCst) {
            return Err(anyhow!("Interrupted by signal"));
        }

        let remaining = (len - written) as usize;
        let to_write = std::cmp::min(remaining, buffer.len());

        rng.fill_bytes(&mut buffer[..to_write]);
        file.write_all(&buffer[..to_write]).context("write random data")?;

        written += to_write as u64;

        // Optimized Progress: Batch updates & Stop if disconnected
        if let Some(ref s) = progress_sender {
            if progress_alive {
                progress_accumulator += to_write as u64;
                
                if progress_accumulator >= PROGRESS_BATCH_SIZE {
                    match s.try_send(progress_accumulator) {
                        Ok(_) => {
                            progress_accumulator = 0;
                        },
                        Err(TrySendError::Full(_)) => {
                            // UI lagging, keep accumulating
                        },
                        Err(TrySendError::Disconnected(_)) => {
                            // Receiver is dead, stop attempting updates
                            progress_alive = false;
                            progress_accumulator = 0;
                        }
                    }
                }
            }
        }

        if let Some(ms) = throttle {
            std::thread::sleep(Duration::from_millis(ms));
        }
    }

    // Send trailing progress
    if progress_alive && progress_accumulator > 0 {
        if let Some(ref s) = progress_sender {
             let _ = s.try_send(progress_accumulator);
        }
    }

    if !RUNNING.load(Ordering::SeqCst) {
        return Err(anyhow!("Interrupted before sync"));
    }

    // Heavy syscalls
    file.sync_data().context("fdatasync")?; 
    file.sync_all().context("fsync")?;

    // --- Pass 2: Verify ---
    if verify {
        if verbose { println!("Verifying data..."); }
        
        rng = StdRng::from_seed(seed);
        file.seek(SeekFrom::Start(0)).context("seek for verify")?;
        
        let mut verify_buf = AlignedBuffer::new(buf_size).context("Failed to alloc verify buffer")?;
        let mut verified: u64 = 0;

        while verified < len {
            if !RUNNING.load(Ordering::SeqCst) {
                return Err(anyhow!("Interrupted during verification"));
            }

            let remaining = (len - verified) as usize;
            let to_read = std::cmp::min(remaining, verify_buf.len());

            rng.fill_bytes(&mut buffer[..to_read]); 
            file.read_exact(&mut verify_buf[..to_read]).context("read for verify")?; 

            if buffer[..to_read] != verify_buf[..to_read] {
                return Err(anyhow!("Verification Failed! Data mismatch."));
            }

            verified += to_read as u64;
        }
    }

    Ok(())
}

fn punch_hole(file: &File, len: u64) -> Result<()> {
    if len > i64::MAX as u64 { return Err(anyhow!("File too large for fallocate")); }
    let fd = file.as_raw_fd();
    let mode = FallocateFlags::FALLOC_FL_PUNCH_HOLE | FallocateFlags::FALLOC_FL_KEEP_SIZE;
    
    match fallocate(fd, mode, 0, len as i64) {
        Ok(_) => Ok(()),
        Err(e) => {
            if e == nix::errno::Errno::EOPNOTSUPP || e == nix::errno::Errno::ENOSYS {
                return Err(anyhow!("TRIM not supported by filesystem"));
            }
            Err(anyhow!("fallocate failed: {}", e))
        }
    }
}

fn random_name() -> String {
    rand::thread_rng().sample_iter(&Alphanumeric).take(12).map(char::from).collect()
}

fn sync_parent(path: &Path) {
    if let Some(parent) = path.parent() {
        if let Ok(dir) = OpenOptions::new().read(true).open(parent) {
            let _ = dir.sync_all();
        }
    }
}

fn secure_wipe_file(path: &Path, progress_sender: Option<Sender<u64>>, args: &Cli, logger: &Arc<AuditLogger>, stats: &Arc<WipeStats>) -> Result<()> {
    let meta = fs::symlink_metadata(path).with_context(|| format!("stat {:?}", path))?;

    if !meta.is_file() { return Ok(()); }

    if meta.nlink() > 1 {
        if !args.allow_hardlinks {
            let msg = format!("Skipping {:?}: {} hard links (Use --allow-hardlinks to force).", path, meta.nlink());
            logger.log(&msg);
            eprintln!("{}", msg);
            stats.skipped.fetch_add(1, Ordering::Relaxed);
            return Ok(());
        }
    }

    if is_network_or_overlay(path) && args.verbose {
        eprintln!("Warning: {:?} is on Network/Overlay FS.", path);
    }

    if args.dry_run {
        println!("DRY-RUN: Would wipe {:?}", path);
        return Ok(());
    }

    let mut options = OpenOptions::new();
    options.write(true);
    options.read(true);
    options.custom_flags(libc::O_NOFOLLOW | libc::O_SYNC); 

    let mut file = match options.open(path) {
        Ok(f) => {
            let f_meta = f.metadata()?;
            if f_meta.ino() != meta.ino() || f_meta.dev() != meta.dev() {
                let msg = format!("Security Warning: {:?} replaced during operation. Skipping.", path);
                logger.log(&msg);
                eprintln!("{}", msg);
                stats.skipped.fetch_add(1, Ordering::Relaxed);
                return Ok(());
            }
            f
        },
        Err(e) => {
            if e.raw_os_error() == Some(libc::ELOOP) {
                let msg = format!("Skipping {:?}: Symlink detected during open.", path);
                logger.log(&msg);
                stats.skipped.fetch_add(1, Ordering::Relaxed);
                return Ok(());
            }
            if e.kind() == std::io::ErrorKind::PermissionDenied {
                if Uid::effective().is_root() {
                    let f_ro = OpenOptions::new()
                    .read(true)
                    .custom_flags(libc::O_NOFOLLOW)
                    .open(path)
                    .context("Failed to open file for immutable check")?;

                    if let Err(err) = remove_immutable_flag(f_ro.as_raw_fd()) {
                        return Err(anyhow!("Failed to clear immutable flag: {}", err));
                    }
                    drop(f_ro);
                    options.open(path)?
                } else {
                    return Err(anyhow!("Permission denied (immutable file?). Root required."));
                }
            } else {
                return Err(anyhow!("Open failed: {}", e));
            }
        }
    };

    // TOCTOU Fix: Use current fd length
    let len = file.metadata()?.len();

    if let Err(e) = overwrite_file(&mut file, len, progress_sender, args.throttle_ms, args.verify, args.verbose) {
        let msg = format!("Overwrite/Verify failed {:?}: {}. ABORTING DELETE.", path, e);
        logger.log(&msg);
        stats.failed.fetch_add(1, Ordering::Relaxed);
        if args.verify {
            stats.verified_errors.fetch_add(1, Ordering::Relaxed);
        }
        return Err(anyhow!("{}", msg));
    }

    if let Err(e) = punch_hole(&file, len) {
        if args.verbose { eprintln!("Info: TRIM unsupported {:?}: {}", path, e); }
    }

    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    let obf = parent.join(format!(".tmp_{}", random_name()));

    let rename_ok = fs::rename(path, &obf).is_ok();
    
    let target_to_remove = if rename_ok { 
        sync_parent(&obf);
        obf 
    } else { 
        path.to_path_buf() 
    };

    drop(file);

    if let Err(e) = fs::remove_file(&target_to_remove) {
        let msg = format!("Removal failed {:?}: {}", target_to_remove, e);
        logger.log(&msg);
        stats.failed.fetch_add(1, Ordering::Relaxed);
        return Err(anyhow!("{}", msg));
    }

    sync_parent(&target_to_remove);
    logger.log(&format!("Deleted: {:?}", path));
    stats.deleted.fetch_add(1, Ordering::Relaxed);
    return Ok(());
}

fn device_sanitize(device: &Path, yes: bool) -> Result<()> {
    if !Uid::effective().is_root() {
        return Err(anyhow!("Root privileges required."));
    }

    let meta = fs::metadata(device).context("Stat device failed")?;
    if !meta.file_type().is_block_device() {
        return Err(anyhow!("Not a block device: {:?}", device));
    }

    let nvme_check = Command::new("nvme").arg("--version").output();
    match nvme_check {
        Ok(out) if out.status.success() => {},
        Ok(out) => return Err(anyhow!("'nvme-cli' check failed: {}", String::from_utf8_lossy(&out.stderr).trim())),
        Err(e) => return Err(anyhow!("Failed to execute 'nvme': {}. Please install nvme-cli.", e)),
    }

    if !yes {
        eprintln!("WARNING: DEVICE SANITIZE IS DESTRUCTIVE!");
        eprintln!("   This will erase ALL data on {:?} instantly.", device);
        eprint!("   Type 'YES' to continue: ");
        let mut input = String::new();
        std::io::stdin().read_line(&mut input)?;
        if input.trim() != "YES" { return Err(anyhow!("Aborted")); }
    }

    println!("Initiating NVMe Sanitize...");
    println!("Info: Command returns immediately; sanitize runs in background.");

    let output = Command::new("nvme")
    .args(&["sanitize", "-a", "start-crypto-erase"])
    .arg(device.as_os_str())
    .output()
    .context("Failed to execute nvme-cli")?;

    if output.status.success() {
        println!("Sanitize command issued (Crypto Erase).");
        println!("Verify status with: sudo nvme sanitize-log {:?}", device);
        return Ok(());
    }

    eprintln!("Crypto Erase failed, trying Block Erase (slower)...");

    let output_block = Command::new("nvme")
    .args(&["sanitize", "-a", "start-block-erase"])
    .arg(device.as_os_str())
    .output()?;

    if output_block.status.success() {
        println!("Block Erase command issued.");
        return Ok(());
    }

    Err(anyhow!("Sanitize failed: {}", String::from_utf8_lossy(&output_block.stderr)))
}

fn main() -> Result<()> {
    ctrlc::set_handler(|| {
        RUNNING.store(false, Ordering::SeqCst);
    }).expect("Error setting Ctrl-C handler");

    let args = Cli::parse();
    let logger = Arc::new(AuditLogger::new(args.log_file.clone())?);
    let stats = Arc::new(WipeStats::new());

    if args.sanitize {
        let device = args.device.as_ref().ok_or_else(|| anyhow!("--sanitize requires --device"))?;
        return device_sanitize(device, args.yes);
    }

    let mut total_bytes: u64 = 0;

    if args.verbose { println!("Scanning targets..."); }

    for p in &args.files {
        for entry in WalkDir::new(p) {
            if !RUNNING.load(Ordering::SeqCst) { break; }
            if let Ok(e) = entry {
                if e.file_type().is_file() {
                    if !args.no_progress {
                        total_bytes = total_bytes.saturating_add(e.metadata().map(|m| m.len()).unwrap_or(0));
                    }
                }
            }
        }
    }

    if !RUNNING.load(Ordering::SeqCst) {
        eprintln!("Aborted by signal.");
        std::process::exit(130);
    }

    let (tx, rx) = bounded::<u64>(8192);

    let pb_thread = if !args.no_progress && total_bytes > 0 {
        let pb = Arc::new(ProgressBar::new(total_bytes));
        pb.set_style(ProgressStyle::default_bar()
        .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {bytes}/{total_bytes} ({eta})")?
        .progress_chars("#>-"));

        let pb_clone = pb.clone();
        Some(std::thread::spawn(move || {
            for inc in rx { pb_clone.inc(inc); }
            pb_clone.finish_with_message("Done");
        }))
    } else {
        None
    };

    let pool = rayon::ThreadPoolBuilder::new().num_threads(args.jobs).build()?;

    pool.install(|| {
        let all_files = args.files.iter().flat_map(|p| WalkDir::new(p));

        all_files.par_bridge().for_each(|entry| {
            if !RUNNING.load(Ordering::SeqCst) { return; }

            match entry {
                Ok(e) => {
                    if e.file_type().is_file() {
                        let sender = if !args.no_progress { Some(tx.clone()) } else { None };
                        if let Err(err) = secure_wipe_file(e.path(), sender, &args, &logger, &stats) {
                            eprintln!("Error {:?}: {}", e.path(), err);
                        }
                    }
                },
                Err(err) => if args.verbose { eprintln!("Walk error: {}", err); }
            }
        });
    });

    drop(tx);
    if let Some(t) = pb_thread {
        if let Err(e) = t.join() {
            eprintln!("Progress thread panicked: {:?}", e);
        }
    }

    if !args.no_progress && total_bytes > 0 {
        eprintln!();
    }

    if !args.dry_run && RUNNING.load(Ordering::SeqCst) {
        for p in &args.files {
            if p.is_dir() {
                for entry in WalkDir::new(p).contents_first(true) {
                    if let Ok(e) = entry {
                        if e.file_type().is_dir() {
                            let _ = fs::remove_dir(e.path());
                        }
                    }
                }
                let _ = fs::remove_dir(p);
            }
        }
    }

    if !RUNNING.load(Ordering::SeqCst) {
        eprintln!("Aborted by signal.");
        std::process::exit(130);
    }

    let s_del = stats.deleted.load(Ordering::Relaxed);
    let s_skip = stats.skipped.load(Ordering::Relaxed);
    let s_fail = stats.failed.load(Ordering::Relaxed);
    let s_ver_err = stats.verified_errors.load(Ordering::Relaxed);

    if s_del == 0 && s_skip == 0 && s_fail == 0 && !args.dry_run {
        println!("No regular files found to wipe.");
    } else {
        println!("Summary: {} deleted, {} skipped, {} failed.", s_del, s_skip, s_fail);
        if s_ver_err > 0 {
            eprintln!("CRITICAL: {} files failed verification (possible bad sectors or SSD cache persistence).", s_ver_err);
        }
    }

    if s_fail > 0 || s_ver_err > 0 {
        std::process::exit(1);
    }

    Ok(())
}
