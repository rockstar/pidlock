//! # pidlock
//!
//! A library for creating and managing PID-based file locks, providing a simple and reliable
//! way to ensure only one instance of a program runs at a time.
//!
//! ## Features
//!
//! - **Cross-platform**: Works on Unix-like systems and Windows
//! - **Stale lock detection**: Automatically detects and cleans up locks from dead processes
//! - **Path validation**: Ensures lock file paths are valid across platforms
//! - **Safe cleanup**: Automatically releases locks when the `Pidlock` is dropped
//! - **Comprehensive error handling**: Detailed error types for different failure scenarios
//!
//! ## Quick Start
//!
//! ```rust
//! use pidlock::Pidlock;
//! use std::path::Path;
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let temp_dir = std::env::temp_dir();
//! let lock_path = temp_dir.join("my_app.pid");
//! let mut lock = Pidlock::new_validated(&lock_path)?;
//!
//! // Try to acquire the lock
//! match lock.acquire() {
//!     Ok(()) => {
//!         println!("Lock acquired successfully!");
//!         
//!         // Do your work here...
//!         
//!         // Explicitly release the lock (optional - it's auto-released on drop)
//!         lock.release()?;
//!         println!("Lock released successfully!");
//!     }
//!     Err(pidlock::PidlockError::LockExists) => {
//!         println!("Another instance is already running");
//!     }
//!     Err(e) => {
//!         eprintln!("Failed to acquire lock: {}", e);
//!     }
//! }
//! # Ok(())
//! # }
//! ```
//!
//! ## Advanced Usage
//!
//! ### Checking Lock Status Without Acquiring
//!
//! ```rust
//! use pidlock::Pidlock;
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let temp_dir = std::env::temp_dir();
//! let lock_path = temp_dir.join("example.pid");
//! let lock = Pidlock::new_validated(&lock_path)?;
//!
//! // Check if a lock file exists
//! if lock.exists() {
//!     // Check if the lock is held by an active process
//!     match lock.is_active()? {
//!         true => println!("Lock is held by an active process"),
//!         false => println!("Lock file exists but process is dead (stale lock)"),
//!     }
//! } else {
//!     println!("No lock file exists");
//! }
//! # Ok(())
//! # }
//! ```
//!
//! ### Error Handling
//!
//! ```rust
//! use pidlock::{Pidlock, PidlockError, InvalidPathError};
//!
//! # fn main() {
//! let result = Pidlock::new_validated("invalid<path>");
//! match result {
//!     Ok(_) => println!("Path is valid"),
//!     Err(PidlockError::InvalidPath(InvalidPathError::ProblematicCharacter { character, filename })) => {
//!         println!("Invalid character '{}' in filename: {}", character, filename);
//!     }
//!     Err(e) => println!("Other error: {}", e),
//! }
//! # }
//! ```
//!
//! ## Platform Considerations
//!
//! - **Unix/Linux**: Uses POSIX signals for process detection, respects umask for permissions
//! - **Windows**: Uses Win32 APIs for process detection, handles reserved filenames
//! - **File permissions**: Lock files are created with restrictive permissions (600 on Unix)
//! - **Path validation**: Automatically validates paths for cross-platform compatibility
//! - **Lock file locations**: Use `/run/lock/` on Linux, `/var/run/` on other Unix systems,
//!   or appropriate system directories. Avoid `/tmp` for production use.
//!
//! ## Safety
//!
//! This library uses unsafe code for platform-specific process detection, but all unsafe
//! operations are carefully validated and documented. The library ensures that:
//!
//! - PID values are validated before use in system calls
//! - Windows handles are properly managed and cleaned up
//! - Unix signals are used safely without affecting target processes

use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::{fs, process};

use thiserror::Error;

#[cfg(feature = "log")]
use log::warn;

/// Specific types of path validation errors.
///
/// These errors occur when the provided path for a lock file is not suitable
/// for cross-platform use or contains problematic characters.
///
/// # Examples
///
/// ```rust
/// use pidlock::{Pidlock, PidlockError, InvalidPathError};
///
/// // Example of catching specific path validation errors
/// match Pidlock::new_validated("") {
///     Err(PidlockError::InvalidPath(InvalidPathError::EmptyPath)) => {
///         println!("Path cannot be empty");
///     }
///     _ => {}
/// }
/// ```
#[derive(Debug, Error)]
pub enum InvalidPathError {
    #[error("Path cannot be empty")]
    EmptyPath,

    #[error("Filename '{filename}' is reserved on Windows")]
    ReservedName { filename: String },

    #[error("Filename contains problematic character '{character}': {filename}")]
    ProblematicCharacter { character: char, filename: String },

    #[error("Filename contains control characters: {filename}")]
    ControlCharacters { filename: String },

    #[error("Cannot create parent directory {path}")]
    ParentDirectoryCreationFailed {
        path: String,
        #[source]
        source: std::io::Error,
    },
}

/// Errors that may occur during the `Pidlock` lifetime.
///
/// This enum covers all possible error conditions that can occur when working
/// with pidlocks, from path validation to I/O errors during lock operations.
///
/// # Examples
///
/// ```rust
/// use pidlock::{Pidlock, PidlockError};
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let temp_dir = std::env::temp_dir();
/// let lock_path = temp_dir.join("error_example.pid");
/// let mut lock = Pidlock::new_validated(&lock_path)?;
///
/// match lock.acquire() {
///     Ok(()) => {
///         println!("Lock acquired successfully");
///         lock.release()?;
///     }
///     Err(PidlockError::LockExists) => {
///         println!("Another process is holding the lock");
///     }
///     Err(PidlockError::InvalidState) => {
///         println!("Lock is in wrong state for this operation");
///     }
///     Err(e) => {
///         println!("Other error: {}", e);
///     }
/// }
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum PidlockError {
    #[error("A lock already exists")]
    LockExists,

    #[error("An operation was attempted in the wrong state, e.g. releasing before acquiring")]
    InvalidState,

    #[error("An I/O error occurred")]
    IOError(#[from] std::io::Error),

    #[error("Invalid path provided for lock file")]
    InvalidPath(#[from] InvalidPathError),
}

impl PartialEq for PidlockError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PidlockError::LockExists, PidlockError::LockExists) => true,
            (PidlockError::InvalidState, PidlockError::InvalidState) => true,
            (PidlockError::IOError(a), PidlockError::IOError(b)) => {
                // Compare IO errors by their kind only (more reliable than string comparison)
                a.kind() == b.kind()
            }
            (PidlockError::InvalidPath(a), PidlockError::InvalidPath(b)) => {
                // Compare InvalidPathError by discriminant only for now
                // This is a simplified comparison since InvalidPathError may contain non-comparable fields
                std::mem::discriminant(a) == std::mem::discriminant(b)
            }
            _ => false,
        }
    }
}

/// A result from a Pidlock operation
type PidlockResult = Result<(), PidlockError>;

/// States a Pidlock can be in during its lifetime.
#[derive(Debug, PartialEq)]
enum PidlockState {
    #[doc = "A new pidlock, unacquired"]
    New,
    #[doc = "A lock is acquired"]
    Acquired,
    #[doc = "A lock is released"]
    Released,
}

/// Validates that a path is suitable for use as a lock file.
/// Checks for common cross-platform path issues.
fn validate_lock_path(path: &Path) -> Result<(), PidlockError> {
    #[cfg(feature = "log")]
    if path.is_relative() {
        warn!(
            "Using relative path for lock file: {:?}. Consider using absolute paths for better reliability.",
            path
        );
    }

    // Check for empty path
    if path.as_os_str().is_empty() {
        return Err(PidlockError::InvalidPath(InvalidPathError::EmptyPath));
    }

    // Check for common problematic characters in filename
    if let Some(filename) = path.file_name() {
        let filename_str = filename.to_string_lossy();

        // Check for reserved names on Windows
        #[cfg(target_os = "windows")]
        {
            let reserved_names = [
                "CON", "PRN", "AUX", "NUL", "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7",
                "COM8", "COM9", "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8",
                "LPT9",
            ];
            let base_name = filename_str
                .split('.')
                .next()
                .unwrap_or(&filename_str)
                .to_uppercase();
            if reserved_names.contains(&base_name.as_str()) {
                return Err(PidlockError::InvalidPath(InvalidPathError::ReservedName {
                    filename: filename_str.to_string(),
                }));
            }
        }

        // Check for problematic characters
        let problematic_chars = ['<', '>', ':', '"', '|', '?', '*'];
        for &ch in &problematic_chars {
            if filename_str.contains(ch) {
                return Err(PidlockError::InvalidPath(
                    InvalidPathError::ProblematicCharacter {
                        character: ch,
                        filename: filename_str.to_string(),
                    },
                ));
            }
        }

        // Check for control characters
        if filename_str.chars().any(|c| c.is_control()) {
            return Err(PidlockError::InvalidPath(
                InvalidPathError::ControlCharacters {
                    filename: filename_str.to_string(),
                },
            ));
        }
    }

    // Try to validate parent directory exists or can be created
    if let Some(parent) = path.parent()
        && !parent.exists()
    {
        // Check if we can potentially create the directory
        if let Err(e) = fs::create_dir_all(parent) {
            return Err(PidlockError::InvalidPath(
                InvalidPathError::ParentDirectoryCreationFailed {
                    path: parent.display().to_string(),
                    source: e,
                },
            ));
        }
    }

    Ok(())
}

/// Validates that a PID is within reasonable bounds for the current system.
fn validate_pid(pid: i32) -> bool {
    // PIDs should be positive
    if pid <= 0 {
        return false;
    }

    // Check against system-specific limits
    #[cfg(target_os = "linux")]
    {
        // Try to read the actual maximum PID from /proc/sys/kernel/pid_max
        // If that fails, fall back to the typical default of 2^22 (4194304)
        let max_pid = match fs::read_to_string("/proc/sys/kernel/pid_max") {
            Ok(content) => match content.trim().parse::<i32>() {
                Ok(parsed_max) => parsed_max,
                Err(_parse_err) => {
                    #[cfg(feature = "log")]
                    warn!(
                        "Failed to parse /proc/sys/kernel/pid_max content '{}': {}, using default 4194304",
                        content.trim(),
                        _parse_err
                    );
                    4194304
                }
            },
            Err(_read_err) => {
                #[cfg(feature = "log")]
                warn!(
                    "Failed to read /proc/sys/kernel/pid_max: {}, using default 4194304",
                    _read_err
                );
                4194304
            }
        };

        pid <= max_pid
    }

    #[cfg(target_os = "macos")]
    {
        // macOS defines PID_MAX as 99999, but process IDs are not assigned
        // to PID_MAX, so max pid is 99998.
        pid < 99999
    }

    #[cfg(target_os = "windows")]
    {
        // Windows uses 32-bit process IDs
        // pid <= i32::MAX will always return true
        true
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
    {
        // Conservative default for other Unix-like systems
        pid <= 99999
    }
}

/// Check whether a process exists, used to determine whether a pid file is stale.
///
/// This function uses platform-specific system calls to check process existence
/// without sending signals or affecting the target process.
///
/// # Arguments
/// * `pid` - Process ID to check. Must be a positive integer within platform limits.
///
/// # Returns
/// * `true` if the process exists and is accessible
/// * `false` if the process doesn't exist, has exited, or we lack permissions
///
/// # Safety
/// This function is safe when called with validated PIDs because:
/// - On Windows: Uses safe Win32 APIs with proper handle management and error checking
/// - On Unix: Uses the POSIX null signal (sig=0) which only performs permission checks
fn process_exists(pid: i32) -> bool {
    // Validate PID range before any unsafe operations
    if !validate_pid(pid) {
        return false;
    }

    #[cfg(target_os = "windows")]
    {
        // SAFETY: The `windows` crate does not provide a completely safe interface. Rather,
        // it provides a "more safe" interface. As such, there is no safe API for windows.
        // We use Windows APIs according to their documented contracts:
        // - OpenProcess is called with valid flags and a validated positive PID
        // - We check return values before using handles
        // - CloseHandle is always called to prevent resource leaks
        // - GetExitCodeProcess is only called with a valid handle
        // The PID has already been validated by validate_pid() to be positive and within range
        use windows::Win32::Foundation::{CloseHandle, HANDLE, NTSTATUS, STILL_ACTIVE};
        use windows::Win32::System::Threading::{
            GetExitCodeProcess, OpenProcess, PROCESS_QUERY_INFORMATION,
        };

        let handle = unsafe {
            match OpenProcess(PROCESS_QUERY_INFORMATION, false, pid as u32) {
                Ok(h) => h,
                Err(_) => {
                    // OpenProcess failed, likely due to invalid PID or insufficient permissions
                    return false;
                }
            }
        };

        // Check if OpenProcess failed (returns 0 or INVALID_HANDLE_VALUE)
        if handle.is_invalid() {
            // Process doesn't exist or we don't have permission to query it
            return false;
        }

        // Use RAII-style cleanup to ensure handle is always closed, even on panic
        struct HandleGuard(HANDLE);
        impl Drop for HandleGuard {
            fn drop(&mut self) {
                let _ = unsafe { CloseHandle(self.0) };
            }
        }
        let _guard = HandleGuard(handle);

        let mut exit_code: u32 = 0;
        unsafe {
            match GetExitCodeProcess(handle, &mut exit_code) {
                Ok(_) => {
                    // Return true only if GetExitCodeProcess succeeded AND process is still active
                    // Note: STILL_ACTIVE (259) could theoretically be a real exit code, but it's
                    // extremely unlikely in practice. This is the documented Windows API pattern
                    // for checking if a process is still running. The risk of false positives
                    // (a process that actually exited with code 259) is negligible.
                    NTSTATUS(exit_code as i32) == STILL_ACTIVE
                }
                Err(_) => false, // GetExitCodeProcess failed
            }
        }
    }

    #[cfg(not(target_os = "windows"))]
    {
        // We specify None as the signal, which equates to using 0 in `kill(2)`. This
        // means no signal is sent, but error checking is still performed.
        nix::sys::signal::kill(nix::unistd::Pid::from_raw(pid), None).is_ok()
    }
}

/// A pid-centered lock. A lock is considered "acquired" when a file exists on disk
/// at the path specified, containing the process id of the locking process.
///
/// ## Examples
///
/// ### Basic Usage
///
/// ```rust
/// use pidlock::Pidlock;
/// use std::fs;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// // Create a lock in a temporary location
/// let temp_dir = std::env::temp_dir();
/// let lock_path = temp_dir.join("example.pid");
///
/// let mut lock = Pidlock::new_validated(&lock_path)?;
///
/// // Acquire the lock
/// lock.acquire()?;
/// assert!(lock.locked());
///
/// // The lock file now exists and contains our PID
/// assert!(lock.exists());
///
/// // Release the lock
/// lock.release()?;
/// assert!(!lock.locked());
/// assert!(!lock.exists()); // File is removed
/// # Ok(())
/// # }
/// ```
///
/// ### Handling Lock Conflicts
///
/// ```rust
/// use pidlock::{Pidlock, PidlockError};
/// use std::fs;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let temp_dir = std::env::temp_dir();
/// let lock_path = temp_dir.join("conflict_example.pid");
///
/// // First lock
/// let mut lock1 = Pidlock::new_validated(&lock_path)?;
/// lock1.acquire()?;
///
/// // Try to acquire the same lock from another instance
/// let mut lock2 = Pidlock::new_validated(&lock_path)?;
/// match lock2.acquire() {
///     Err(PidlockError::LockExists) => {
///         println!("Lock is already held by another process");
///         // This is expected behavior
///     }
///     _ => panic!("Should have failed with LockExists"),
/// }
///
/// // Clean up
/// lock1.release()?;
/// # Ok(())
/// # }
/// ```
///
/// ### Automatic Cleanup on Drop
///
/// ```rust
/// use pidlock::Pidlock;
/// use std::fs;
///
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let temp_dir = std::env::temp_dir();
/// let lock_path = temp_dir.join("drop_example.pid");
///
/// {
///     let mut lock = Pidlock::new_validated(&lock_path)?;
///     lock.acquire()?;
///     assert!(lock.exists());
///     // Lock goes out of scope here and is automatically cleaned up
/// }
///
/// // Lock file should be removed by the Drop implementation
/// assert!(!lock_path.exists());
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct Pidlock {
    #[doc = "The current process id"]
    pid: u32,
    #[doc = "A path to the lock file"]
    path: PathBuf,
    #[doc = "Current state of the Pidlock"]
    state: PidlockState,
}

impl Pidlock {
    /// Create a new Pidlock at the provided path.
    ///
    /// For backwards compatibility, this method does not validate the path.
    /// Use `new_validated` if you want path validation.
    #[deprecated(
        since = "0.2.0",
        note = "Use `new_validated` for path validation and better cross-platform compatibility"
    )]
    pub fn new(path: impl AsRef<Path>) -> Self {
        Pidlock {
            pid: process::id(),
            path: path.as_ref().into(),
            state: PidlockState::New,
        }
    }

    /// Create a new Pidlock at the provided path with path validation.
    ///
    /// This is the recommended way to create a `Pidlock` as it validates the path
    /// for cross-platform compatibility and common issues.
    ///
    /// # Arguments
    ///
    /// * `path` - The path where the lock file will be created. The parent directory
    ///   must exist or be creatable.
    ///
    /// # Returns
    ///
    /// * `Ok(Pidlock)` - A new pidlock instance ready to be acquired
    /// * `Err(PidlockError::InvalidPath)` - If the path is not suitable for use as a lock file
    ///
    /// # Examples
    ///
    /// ```rust
    /// use pidlock::Pidlock;
    /// use std::env;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// // Valid path
    /// let temp_dir = env::temp_dir();
    /// let lock_path = temp_dir.join("valid.pid");
    /// let lock = Pidlock::new_validated(&lock_path)?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// ```rust
    /// use pidlock::{Pidlock, PidlockError, InvalidPathError};
    ///
    /// # fn main() {
    /// // Invalid path with problematic characters
    /// let result = Pidlock::new_validated("invalid<file.pid");
    /// match result {
    ///     Err(PidlockError::InvalidPath(InvalidPathError::ProblematicCharacter { .. })) => {
    ///         // Expected error for invalid characters
    ///     }
    ///     _ => panic!("Should have failed with InvalidPath"),
    /// }
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns `PidlockError::InvalidPath` if the path is not suitable for use as a lock file.
    pub fn new_validated(path: impl AsRef<Path>) -> Result<Self, PidlockError> {
        let path_ref = path.as_ref();

        // Validate the path before creating the Pidlock
        validate_lock_path(path_ref)?;

        Ok(Pidlock {
            pid: process::id(),
            path: path_ref.into(),
            state: PidlockState::New,
        })
    }

    /// Check whether a lock file already exists, and if it does, whether the
    /// specified pid is still a valid process id on the system.
    /// Returns true if the lock exists but the process is no longer running.
    fn check_stale(&self) -> bool {
        // First check if the lock file even exists
        if !self.path.exists() {
            return false;
        }

        // Try to get the owner PID - if this fails, we can't determine if it's stale
        match self.get_owner() {
            Ok(Some(pid)) => {
                // We have a valid PID, check if the process is still running
                !process_exists(pid)
            }
            Ok(None) => {
                // No PID found in file, consider it stale
                true
            }
            Err(_) => {
                // Error reading the file, can't determine staleness safely
                false
            }
        }
    }

    /// Acquire a lock.
    ///
    /// This method attempts to create the lock file containing the current process ID.
    /// If a stale lock file exists (from a dead process), it will be automatically cleaned up.
    ///
    /// # Returns
    ///
    /// * `Ok(())` - Lock was successfully acquired
    /// * `Err(PidlockError::LockExists)` - Another active process holds the lock
    /// * `Err(PidlockError::InvalidState)` - Lock is already acquired or released
    /// * `Err(PidlockError::IOError)` - File system error occurred
    ///
    /// # Examples
    ///
    /// ```rust
    /// use pidlock::{Pidlock, PidlockError};
    /// use std::env;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let temp_dir = env::temp_dir();
    /// let lock_path = temp_dir.join("acquire_example.pid");
    ///
    /// let mut lock = Pidlock::new_validated(&lock_path)?;
    ///
    /// match lock.acquire() {
    ///     Ok(()) => {
    ///         println!("Lock acquired successfully!");
    ///         // Do your work here...
    ///         lock.release()?;
    ///     }
    ///     Err(PidlockError::LockExists) => {
    ///         println!("Another instance is already running");
    ///     }
    ///     Err(e) => {
    ///         eprintln!("Unexpected error: {}", e);
    ///     }
    /// }
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Behavior
    ///
    /// 1. **State validation**: Can only be called on a `New` pidlock
    /// 2. **Stale lock cleanup**: Automatically removes locks from dead processes
    /// 3. **Atomic creation**: Uses `O_EXCL`/`CREATE_NEW` for atomic lock file creation
    /// 4. **Secure permissions**: Creates files with restrictive permissions (600 on Unix)
    /// 5. **Reliable writes**: Flushes data to disk before returning success
    pub fn acquire(&mut self) -> PidlockResult {
        match self.state {
            PidlockState::New => {}
            _ => {
                return Err(PidlockError::InvalidState);
            }
        }

        // Check if there's a stale lock that we can remove
        if self.check_stale() {
            // Lock exists but process is dead, remove the stale lock file
            let _ = fs::remove_file(&self.path);
        }

        // Create file with appropriate permissions
        let mut options = fs::OpenOptions::new();
        options.create_new(true).write(true);

        // Set restrictive permissions on Unix-like systems for security
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.mode(0o600);
        }

        let mut file = match options.open(&self.path) {
            Ok(file) => file,
            Err(err) => {
                return match err.kind() {
                    std::io::ErrorKind::AlreadyExists => Err(PidlockError::LockExists),
                    _ => Err(PidlockError::from(err)),
                };
            }
        };

        file.write_all(&self.pid.to_string().into_bytes()[..])
            .map_err(PidlockError::from)?;

        // Ensure data is written to disk for reliability
        file.flush().map_err(PidlockError::from)?;

        self.state = PidlockState::Acquired;
        Ok(())
    }

    /// Returns true when the lock is in an acquired state.
    ///
    /// This is a local state check only - it tells you whether this `Pidlock` instance
    /// has successfully acquired a lock, but doesn't check if the lock file still exists
    /// on disk or if another process might have interfered with it.
    ///
    /// # Returns
    ///
    /// `true` if this `Pidlock` instance has acquired the lock, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use pidlock::Pidlock;
    /// use std::env;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let temp_dir = env::temp_dir();
    /// let lock_path = temp_dir.join("locked_example.pid");
    ///
    /// let mut lock = Pidlock::new_validated(&lock_path)?;
    ///
    /// // Initially not locked
    /// assert!(!lock.locked());
    ///
    /// // After acquiring
    /// lock.acquire()?;
    /// assert!(lock.locked());
    ///
    /// // After releasing
    /// lock.release()?;
    /// assert!(!lock.locked());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Note
    ///
    /// For checking if a lock file exists on disk, use [`exists()`](Self::exists).
    /// For checking if a lock is held by an active process, use [`is_active()`](Self::is_active).
    pub fn locked(&self) -> bool {
        self.state == PidlockState::Acquired
    }

    /// Check if the lock file exists on disk.
    /// This is a read-only operation that doesn't modify the lock state.
    ///
    /// # Returns
    ///
    /// `true` if the lock file exists, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use pidlock::Pidlock;
    /// use std::env;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let temp_dir = env::temp_dir();
    /// let lock_path = temp_dir.join("exists_example.pid");
    ///
    /// let lock = Pidlock::new_validated(&lock_path)?;
    ///
    /// // Initially, no lock file exists
    /// assert!(!lock.exists());
    ///
    /// // Create a lock file manually to test
    /// std::fs::write(&lock_path, "12345")?;
    /// assert!(lock.exists());
    ///
    /// // Clean up
    /// std::fs::remove_file(&lock_path)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn exists(&self) -> bool {
        self.path.exists()
    }

    /// Check if the lock file exists and if so, whether it's stale (owned by a dead process).
    /// This is a read-only operation that doesn't modify the lock state.
    ///
    /// # Returns
    ///
    /// `Ok(true)` if a lock exists and the owning process is still running,
    /// `Ok(false)` if no lock exists or the lock is stale,
    /// `Err(_)` if there was an error determining the lock status.
    ///
    /// # Examples
    ///
    /// ```
    /// use pidlock::Pidlock;
    /// use std::env;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let temp_dir = env::temp_dir();
    /// let lock_path = temp_dir.join("is_active_example.pid");
    ///
    /// let lock = Pidlock::new_validated(&lock_path)?;
    ///
    /// match lock.is_active()? {
    ///     true => println!("Lock is held by an active process"),
    ///     false => println!("No active lock found"),
    /// }
    ///
    /// // Test with our own process
    /// std::fs::write(&lock_path, std::process::id().to_string())?;
    /// assert!(lock.is_active()?); // Our process is definitely active
    ///
    /// // Clean up
    /// std::fs::remove_file(&lock_path)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn is_active(&self) -> Result<bool, PidlockError> {
        if !self.path.exists() {
            return Ok(false);
        }

        match self.get_owner()? {
            Some(pid) => Ok(process_exists(pid)),
            None => Ok(false), // No PID in file means inactive
        }
    }

    /// Release the lock.
    ///
    /// This method removes the lock file from disk and transitions the lock to the `Released` state.
    /// Once released, the lock cannot be re-acquired (create a new `Pidlock` instance instead).
    ///
    /// # Returns
    ///
    /// * `Ok(())` - Lock was successfully released
    /// * `Err(PidlockError::InvalidState)` - Lock is not currently acquired
    /// * `Err(PidlockError::IOError)` - File system error occurred during removal
    ///
    /// # Examples
    ///
    /// ```rust
    /// use pidlock::Pidlock;
    /// use std::env;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let temp_dir = env::temp_dir();
    /// let lock_path = temp_dir.join("release_example.pid");
    ///
    /// let mut lock = Pidlock::new_validated(&lock_path)?;
    /// lock.acquire()?;
    ///
    /// // Explicitly release the lock
    /// lock.release()?;
    ///
    /// // Lock file should be gone
    /// assert!(!lock.exists());
    /// assert!(!lock.locked());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Note
    ///
    /// Releasing a lock is optional - the `Drop` implementation will automatically
    /// clean up acquired locks when the `Pidlock` goes out of scope. However, explicit
    /// release is recommended for better error handling and immediate cleanup.
    pub fn release(&mut self) -> PidlockResult {
        match self.state {
            PidlockState::Acquired => {}
            _ => {
                return Err(PidlockError::InvalidState);
            }
        }

        fs::remove_file(&self.path).map_err(PidlockError::from)?;

        self.state = PidlockState::Released;
        Ok(())
    }

    /// Gets the owner of this lockfile, returning the PID if it exists and is valid.
    ///
    /// This method reads the lock file and attempts to parse the PID contained within.
    /// If the PID is invalid, the process no longer exists, or the file is corrupted,
    /// the lock file will be automatically cleaned up.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(pid))` - Lock file exists and contains a valid PID for an active process
    /// * `Ok(None)` - No lock file exists, or the lock file was invalid and cleaned up
    /// * `Err(_)` - I/O error occurred while reading or cleaning up the file
    ///
    /// # Examples
    ///
    /// ```rust
    /// use pidlock::Pidlock;
    /// use std::env;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let temp_dir = env::temp_dir();
    /// let lock_path = temp_dir.join("owner_example.pid");
    ///
    /// let mut lock = Pidlock::new_validated(&lock_path)?;
    ///
    /// // No owner initially
    /// assert_eq!(lock.get_owner()?, None);
    ///
    /// // After acquiring, we should be the owner
    /// lock.acquire()?;
    /// if let Some(owner_pid) = lock.get_owner()? {
    ///     println!("Lock is owned by PID: {}", owner_pid);
    ///     assert_eq!(owner_pid, std::process::id() as i32);
    /// }
    ///
    /// lock.release()?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Behavior
    ///
    /// This method will automatically clean up lock files in the following cases:
    /// - File contains non-numeric content
    /// - File contains a PID that doesn't correspond to a running process
    /// - File contains a PID outside the valid range for the platform
    /// - File is empty or contains only whitespace
    pub fn get_owner(&self) -> Result<Option<i32>, PidlockError> {
        let mut file = match fs::OpenOptions::new().read(true).open(&self.path) {
            Ok(file) => file,
            Err(_) => {
                return Ok(None);
            }
        };

        let mut contents = String::new();
        if file.read_to_string(&mut contents).is_err() {
            #[cfg(feature = "log")]
            warn!(
                "Removing corrupted/invalid pid file at {}",
                self.path.to_str().unwrap_or("<invalid>")
            );
            fs::remove_file(&self.path).map_err(PidlockError::from)?;
            return Ok(None);
        }

        match contents.trim().parse::<i32>() {
            Ok(pid) if validate_pid(pid) && process_exists(pid) => Ok(Some(pid)),
            Ok(_) => {
                #[cfg(feature = "log")]
                warn!(
                    "Removing stale pid file at {}",
                    self.path.to_str().unwrap_or("<invalid>")
                );
                fs::remove_file(&self.path).map_err(PidlockError::from)?;
                Ok(None)
            }
            Err(_) => {
                #[cfg(feature = "log")]
                warn!(
                    "Removing corrupted/invalid pid file at {}",
                    self.path.to_str().unwrap_or("<invalid>")
                );
                fs::remove_file(&self.path).map_err(PidlockError::from)?;
                Ok(None)
            }
        }
    }
}

impl Drop for Pidlock {
    /// Automatically release the lock when the Pidlock goes out of scope.
    /// This ensures that lock files are cleaned up even if the process panics
    /// or exits unexpectedly while holding a lock.
    ///
    /// Note: This implementation uses a best-effort approach. If cleanup fails,
    /// we don't panic because that could mask the original panic that triggered
    /// the drop. Errors are logged when the `log` feature is enabled.
    fn drop(&mut self) {
        if self.state == PidlockState::Acquired {
            // Best-effort cleanup - we can't return errors from Drop
            match fs::remove_file(&self.path) {
                Ok(()) => {
                    #[cfg(feature = "log")]
                    log::debug!("Successfully cleaned up lock file: {:?}", self.path);
                }
                Err(e) => {
                    #[cfg(feature = "log")]
                    log::warn!(
                        "Failed to remove lock file {:?} during drop: {}. \
                         This may leave a stale lock file on disk.",
                        self.path,
                        e
                    );

                    // Prevent unused variable warning when log feature is disabled
                    #[cfg(not(feature = "log"))]
                    let _ = e;

                    // Silently ignore the error to avoid panicking during drop
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;
    use std::path::PathBuf;

    use rand::distributions::Alphanumeric;
    use rand::{Rng, thread_rng};
    use tempfile::NamedTempFile;

    use super::PidlockState;
    use super::{Pidlock, PidlockError};

    fn make_temp_file() -> NamedTempFile {
        NamedTempFile::new().expect("Failed to create temporary file")
    }

    #[test]
    fn test_new() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let pidfile = Pidlock::new_validated(pid_path).unwrap();

        assert_eq!(pidfile.pid, std::process::id());
        assert_eq!(pidfile.path, PathBuf::from(pid_path));
        assert_eq!(pidfile.state, PidlockState::New);
    }

    #[test]
    fn test_acquire_and_release() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let mut pidfile = Pidlock::new_validated(pid_path).unwrap();
        pidfile.acquire().unwrap();

        assert_eq!(pidfile.state, PidlockState::Acquired);

        pidfile.release().unwrap();

        assert_eq!(pidfile.state, PidlockState::Released);
    }

    #[test]
    fn test_acquire_lock_exists() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let mut orig_pidfile = Pidlock::new_validated(pid_path).unwrap();
        orig_pidfile.acquire().unwrap();

        let mut pidfile = Pidlock::new_validated(orig_pidfile.path.to_str().unwrap()).unwrap();
        match pidfile.acquire() {
            Err(err) => {
                orig_pidfile.release().unwrap();
                assert_eq!(err, PidlockError::LockExists);
            }
            _ => {
                orig_pidfile.release().unwrap();
                panic!("Test failed");
            }
        }
    }

    #[test]
    fn test_acquire_already_acquired() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let mut pidfile = Pidlock::new_validated(pid_path).unwrap();
        pidfile.acquire().unwrap();
        match pidfile.acquire() {
            Err(err) => {
                pidfile.release().unwrap();
                assert_eq!(err, PidlockError::InvalidState);
            }
            _ => {
                pidfile.release().unwrap();
                panic!("Test failed");
            }
        }
    }

    #[test]
    fn test_release_bad_state() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let mut pidfile = Pidlock::new_validated(pid_path).unwrap();
        match pidfile.release() {
            Err(err) => {
                assert_eq!(err, PidlockError::InvalidState);
            }
            _ => {
                panic!("Test failed");
            }
        }
    }

    #[test]
    fn test_locked() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let mut pidfile = Pidlock::new_validated(pid_path).unwrap();
        pidfile.acquire().unwrap();
        assert!(pidfile.locked());
    }

    #[test]
    fn test_locked_not_locked() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let pidfile = Pidlock::new_validated(pid_path).unwrap();
        assert!(!pidfile.locked());
    }

    #[test]
    fn test_stale_pid() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write a random PID to the temp file
        temp_file
            .write_all(&format!("{}", thread_rng().r#gen::<i32>()).into_bytes()[..])
            .unwrap();
        temp_file.flush().unwrap();

        let mut pidfile = Pidlock::new_validated(&path).unwrap();
        pidfile.acquire().unwrap();
        assert_eq!(pidfile.state, PidlockState::Acquired);
    }

    #[test]
    fn test_stale_pid_invalid_contents() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        let contents: String = thread_rng()
            .sample_iter(&Alphanumeric)
            .take(20)
            .map(char::from)
            .collect();
        temp_file.write_all(&contents.into_bytes()).unwrap();
        temp_file.flush().unwrap();

        let mut pidfile = Pidlock::new_validated(&path).unwrap();
        pidfile.acquire().unwrap();
        assert_eq!(pidfile.state, PidlockState::Acquired);
    }

    #[test]
    fn test_stale_pid_corrupted_contents() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        temp_file
            .write_all(&rand::thread_rng().r#gen::<[u8; 32]>())
            .unwrap();
        temp_file.flush().unwrap();

        let mut pidfile = Pidlock::new_validated(&path).unwrap();
        pidfile.acquire().unwrap();
        assert_eq!(pidfile.state, PidlockState::Acquired);
    }

    #[test]
    fn test_drop_cleans_up_lock_file() {
        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Create and acquire a lock in a scope
        {
            let mut pidfile = Pidlock::new_validated(&path).unwrap();
            pidfile.acquire().unwrap();
            assert_eq!(pidfile.state, PidlockState::Acquired);

            // Verify the lock file exists
            assert!(std::path::Path::new(&path).exists());

            // The Drop implementation should clean up when pidfile goes out of scope
        }

        // After the scope ends, the lock file should be cleaned up
        assert!(!std::path::Path::new(&path).exists());
    }

    #[test]
    fn test_drop_only_cleans_up_when_acquired() {
        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Create a lock but don't acquire it
        {
            let _pidfile = Pidlock::new_validated(&path).unwrap();
            // Lock is not acquired, so drop should not try to remove anything
        }

        // Should not have attempted to remove a non-existent lock file
        // (This test mainly ensures no panic occurs during drop)

        // Now create a lock, acquire and manually release it
        {
            let mut pidfile = Pidlock::new_validated(&path).unwrap();
            pidfile.acquire().unwrap();
            pidfile.release().unwrap();
            assert_eq!(pidfile.state, PidlockState::Released);

            // Drop should not try to clean up since state is Released
        }

        // File should already be gone from manual release
        assert!(!std::path::Path::new(&path).exists());
    }

    #[test]
    fn test_get_owner_no_file() {
        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        assert_eq!(result, None);
    }

    #[test]
    fn test_get_owner_valid_pid() {
        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // First create a lock with our own PID
        let mut pidfile = Pidlock::new_validated(&path).unwrap();
        pidfile.acquire().unwrap();

        // Now test get_owner returns our PID
        let result = pidfile.get_owner().unwrap();
        assert_eq!(result, Some(std::process::id() as i32));

        pidfile.release().unwrap();
    }

    #[test]
    fn test_get_owner_empty_file() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write empty content
        temp_file.write_all(b"").unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        // Empty file should be cleaned up and return None
        assert_eq!(result, None);
        assert!(!std::path::Path::new(&path).exists());
    }

    #[test]
    fn test_get_owner_whitespace_only() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write whitespace-only content
        temp_file.write_all(b"   \n  \t  \r\n  ").unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        // Whitespace-only file should be cleaned up and return None
        assert_eq!(result, None);
        assert!(!std::path::Path::new(&path).exists());
    }

    #[test]
    fn test_get_owner_negative_pid() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write a negative PID (which shouldn't exist)
        temp_file.write_all(b"-12345").unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        // Negative PID should be cleaned up and return None
        assert_eq!(result, None);
        assert!(!std::path::Path::new(&path).exists());
    }

    #[test]
    fn test_get_owner_large_pid() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write a very large PID (likely doesn't exist but valid i32)
        let large_pid = i32::MAX;
        temp_file
            .write_all(large_pid.to_string().as_bytes())
            .unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        // Large PID should be cleaned up since it likely doesn't exist
        assert_eq!(result, None);
        assert!(!std::path::Path::new(&path).exists());
    }

    #[test]
    fn test_get_owner_zero_pid() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write PID 0 (which may or may not exist depending on the system)
        temp_file.write_all(b"0").unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();

        // PID 0 behavior is system-dependent:
        // - On some systems (like macOS), PID 0 exists (kernel)
        // - On others, it may not
        // We just verify the method doesn't panic and returns a valid result
        match result {
            Some(0) => {
                // PID 0 exists on this system, file should remain
                assert!(std::path::Path::new(&path).exists());
            }
            None => {
                // PID 0 doesn't exist, file should be cleaned up
                assert!(!std::path::Path::new(&path).exists());
            }
            Some(other) => {
                panic!("Expected PID 0 or None, got Some({})", other);
            }
        }
    }

    #[test]
    fn test_get_owner_mixed_content() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write PID with trailing content that should be ignored
        temp_file.write_all(b"12345 extra content").unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        // Should parse the PID part and clean up since 12345 likely doesn't exist
        assert_eq!(result, None);
        assert!(!std::path::Path::new(&path).exists());
    }

    #[test]
    fn test_concurrent_acquire_attempts() {
        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // First lock should succeed
        let mut lock1 = Pidlock::new_validated(&path).unwrap();
        assert!(lock1.acquire().is_ok());

        // Second lock should fail with LockExists
        let mut lock2 = Pidlock::new_validated(&path).unwrap();
        match lock2.acquire() {
            Err(PidlockError::LockExists) => {} // Expected
            other => panic!("Expected LockExists, got {:?}", other),
        }

        // Clean up
        lock1.release().unwrap();

        // Now second lock should succeed
        assert!(lock2.acquire().is_ok());
        lock2.release().unwrap();
    }

    #[test]
    fn test_acquire_after_stale_cleanup() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write a definitely non-existent PID
        temp_file.write_all(b"999999").unwrap();
        temp_file.flush().unwrap();

        // Acquiring should clean up the stale file and succeed
        let mut pidfile = Pidlock::new_validated(&path).unwrap();
        assert!(pidfile.acquire().is_ok());
        assert_eq!(pidfile.state, PidlockState::Acquired);

        // Verify the file now contains our PID
        let owner = pidfile.get_owner().unwrap();
        assert_eq!(owner, Some(std::process::id() as i32));

        pidfile.release().unwrap();
    }

    #[test]
    fn test_new_validated_valid_path() {
        let temp_file = make_temp_file();
        let path = temp_file.path();

        let pidfile = Pidlock::new_validated(path);
        assert!(pidfile.is_ok());

        let pidfile = pidfile.unwrap();
        assert_eq!(pidfile.pid, std::process::id());
        assert_eq!(pidfile.path, PathBuf::from(path));
        assert_eq!(pidfile.state, PidlockState::New);
    }

    #[test]
    fn test_new_validated_empty_path() {
        let result = Pidlock::new_validated("");
        match result {
            Err(PidlockError::InvalidPath(_)) => {} // Expected
            other => panic!("Expected InvalidPath error, got {:?}", other),
        }
    }

    #[test]
    fn test_new_validated_problematic_characters() {
        // Test various problematic characters
        let problematic_paths = [
            "/tmp/test<file.pid",
            "/tmp/test>file.pid",
            "/tmp/test|file.pid",
            "/tmp/test?file.pid",
            "/tmp/test*file.pid",
        ];

        for path in &problematic_paths {
            let result = Pidlock::new_validated(path);
            match result {
                Err(PidlockError::InvalidPath(_)) => {} // Expected
                other => panic!("Expected InvalidPath for '{}', got {:?}", path, other),
            }
        }
    }

    #[test]
    #[cfg(target_os = "windows")]
    fn test_new_validated_reserved_names_windows() {
        let reserved_paths = [
            "CON.pid", "PRN.pid", "AUX.pid", "NUL.pid", "COM1.pid", "LPT1.pid",
        ];

        for path in &reserved_paths {
            let result = Pidlock::new_validated(path);
            match result {
                Err(PidlockError::InvalidPath(_)) => {} // Expected
                other => panic!("Expected InvalidPath for '{}', got {:?}", path, other),
            }
        }
    }

    #[test]
    fn test_error_display_and_chaining() {
        use super::InvalidPathError;
        use std::error::Error;

        // Test InvalidPathError display
        let empty_path_err = InvalidPathError::EmptyPath;
        assert_eq!(empty_path_err.to_string(), "Path cannot be empty");

        let reserved_name_err = InvalidPathError::ReservedName {
            filename: "CON.pid".to_string(),
        };
        assert_eq!(
            reserved_name_err.to_string(),
            "Filename 'CON.pid' is reserved on Windows"
        );

        let problematic_char_err = InvalidPathError::ProblematicCharacter {
            character: '<',
            filename: "test<file.pid".to_string(),
        };
        assert_eq!(
            problematic_char_err.to_string(),
            "Filename contains problematic character '<': test<file.pid"
        );

        // Test PidlockError display
        let lock_exists_err = PidlockError::LockExists;
        assert_eq!(lock_exists_err.to_string(), "A lock already exists");

        let invalid_state_err = PidlockError::InvalidState;
        assert_eq!(
            invalid_state_err.to_string(),
            "An operation was attempted in the wrong state, e.g. releasing before acquiring"
        );

        // Test error chaining with InvalidPath
        let invalid_path_err = PidlockError::InvalidPath(empty_path_err);
        assert_eq!(
            invalid_path_err.to_string(),
            "Invalid path provided for lock file"
        );

        // Verify error source chain
        if let PidlockError::InvalidPath(inner) = &invalid_path_err {
            assert_eq!(inner.to_string(), "Path cannot be empty");
        }

        // Test that std::error::Error trait is implemented
        let _: &dyn Error = &invalid_path_err;
        let _: &dyn Error = &lock_exists_err;

        // Test IO error chaining (create a simple IO error)
        let io_error = std::io::Error::new(std::io::ErrorKind::PermissionDenied, "test error");
        let parent_dir_err = InvalidPathError::ParentDirectoryCreationFailed {
            path: "/some/path".to_string(),
            source: io_error,
        };

        // Verify error chaining works
        assert_eq!(
            parent_dir_err.to_string(),
            "Cannot create parent directory /some/path"
        );
        assert!(parent_dir_err.source().is_some());

        let pidlock_err = PidlockError::InvalidPath(parent_dir_err);
        assert!(pidlock_err.source().is_some());
    }

    #[test]
    fn test_improved_partial_eq() {
        use super::InvalidPathError;

        // Test that PartialEq works correctly with the new implementation

        // Test simple variants
        assert_eq!(PidlockError::LockExists, PidlockError::LockExists);
        assert_eq!(PidlockError::InvalidState, PidlockError::InvalidState);
        assert_ne!(PidlockError::LockExists, PidlockError::InvalidState);

        // Test IOError comparison by kind only
        let io_err1 = std::io::Error::new(std::io::ErrorKind::PermissionDenied, "message 1");
        let io_err2 = std::io::Error::new(std::io::ErrorKind::PermissionDenied, "message 2");
        let io_err3 = std::io::Error::new(std::io::ErrorKind::NotFound, "message 3");

        let pidlock_io1 = PidlockError::IOError(io_err1);
        let pidlock_io2 = PidlockError::IOError(io_err2);
        let pidlock_io3 = PidlockError::IOError(io_err3);

        // Same error kind should be equal (even with different messages)
        assert_eq!(pidlock_io1, pidlock_io2);
        // Different error kinds should not be equal
        assert_ne!(pidlock_io1, pidlock_io3);

        // Test InvalidPath comparison by discriminant
        let invalid_path1 = PidlockError::InvalidPath(InvalidPathError::EmptyPath);
        let invalid_path2 = PidlockError::InvalidPath(InvalidPathError::EmptyPath);
        let invalid_path3 = PidlockError::InvalidPath(InvalidPathError::ReservedName {
            filename: "CON.pid".to_string(),
        });

        // Same discriminant should be equal
        assert_eq!(invalid_path1, invalid_path2);
        // Different discriminants should not be equal
        assert_ne!(invalid_path1, invalid_path3);
    }

    #[test]
    fn test_error_downcasting() {
        use super::InvalidPathError;
        use std::error::Error;

        // Test error downcasting with proper Error trait implementation
        let invalid_path_err = PidlockError::InvalidPath(InvalidPathError::EmptyPath);

        // Convert to trait object
        let err_trait: &dyn Error = &invalid_path_err;

        // Test downcasting
        assert!(err_trait.downcast_ref::<PidlockError>().is_some());

        // Test source chain navigation
        if let Some(source) = err_trait.source() {
            assert!(source.downcast_ref::<InvalidPathError>().is_some());
        }
    }

    #[test]
    fn test_validate_pid_ranges() {
        use super::validate_pid;

        // Test valid PIDs
        assert!(validate_pid(1));
        assert!(validate_pid(1000));

        // Test invalid PIDs
        assert!(!validate_pid(0));
        assert!(!validate_pid(-1));
        assert!(!validate_pid(-12345));

        // Test system-specific upper bounds
        #[cfg(target_os = "linux")]
        {
            // Read the actual maximum PID from /proc/sys/kernel/pid_max, or use default
            let max_pid = std::fs::read_to_string("/proc/sys/kernel/pid_max")
                .ok()
                .and_then(|content| content.trim().parse::<i32>().ok())
                .unwrap_or(4194304);

            // Test that reasonable PIDs within the max are valid
            assert!(validate_pid(1));
            assert!(validate_pid(std::cmp::min(max_pid, 1000)));

            // Test that max_pid itself is valid
            assert!(validate_pid(max_pid));

            // Test edge cases around the maximum
            if max_pid > 1 {
                assert!(validate_pid(max_pid - 1));
            }

            // Test that max_pid + 1 is invalid (if max_pid < i32::MAX)
            if max_pid < i32::MAX {
                assert!(!validate_pid(max_pid + 1));
            }

            // Test that very large values are invalid
            assert!(!validate_pid(i32::MAX));

            // Ensure the default fallback value (4194304) would be valid
            // This helps ensure our fallback is reasonable
            assert!(max_pid >= 4194304 || validate_pid(4194304));
        }

        #[cfg(target_os = "macos")]
        {
            assert!(validate_pid(99998)); // Should be valid on macOS
            assert!(!validate_pid(99999)); // Should be invalid
        }
    }

    #[test]
    fn test_get_owner_with_invalid_pid_range() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write a PID that's outside valid range (negative)
        temp_file.write_all(b"-500").unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        // Invalid PID should be cleaned up
        assert_eq!(result, None);
        assert!(!std::path::Path::new(&path).exists());
    }

    #[test]
    #[cfg(unix)]
    fn test_file_permissions_unix() {
        use std::os::unix::fs::PermissionsExt;

        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        let mut pidfile = Pidlock::new_validated(&path).unwrap();
        pidfile.acquire().unwrap();

        // Check that file has correct permissions (600 - owner read/write only)
        let metadata = std::fs::metadata(&path).unwrap();
        let mode = metadata.permissions().mode();
        assert_eq!(mode & 0o777, 0o600);

        pidfile.release().unwrap();
    }

    #[test]
    #[cfg(unix)]
    fn test_file_permissions_security() {
        use std::os::unix::fs::PermissionsExt;

        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        let mut pidfile = Pidlock::new_validated(&path).unwrap();
        pidfile.acquire().unwrap();

        let metadata = std::fs::metadata(&path).unwrap();
        let mode = metadata.permissions().mode();

        // Verify the file is NOT readable by group
        assert_eq!(mode & 0o040, 0);
        // Verify the file is NOT readable by others
        assert_eq!(mode & 0o004, 0);
        // Verify the file is NOT writable by group
        assert_eq!(mode & 0o020, 0);
        // Verify the file is NOT writable by others
        assert_eq!(mode & 0o002, 0);

        // Verify the file IS readable and writable by owner
        assert_ne!(mode & 0o400, 0); // Owner read
        assert_ne!(mode & 0o200, 0); // Owner write

        pidfile.release().unwrap();
    }

    #[test]
    fn test_acquire_detailed_error_handling() {
        // Test that we get proper error details instead of generic IOError
        // Test the case where we try to create a lock file that already exists
        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // First, create and acquire a lock
        let mut first_lock = Pidlock::new_validated(&path).unwrap();
        first_lock.acquire().unwrap();

        // Now try to create a second lock on the same file
        let mut second_lock = Pidlock::new_validated(&path).unwrap();
        let result = second_lock.acquire();

        match result {
            Err(PidlockError::LockExists) => {
                // This is the expected behavior - proper error type
            }
            Ok(_) => {
                // This shouldn't happen, but if it does, clean up
                let _ = second_lock.release();
                panic!("Expected LockExists error, but acquire succeeded");
            }
            Err(other) => {
                panic!("Expected LockExists, got {:?}", other);
            }
        }

        // Clean up
        first_lock.release().unwrap();
    }

    #[test]
    fn test_process_exists_safety_edge_cases() {
        // This test verifies that our safety improvements correctly handle edge cases
        // that could previously cause undefined behavior or resource leaks

        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Test Case 1: Negative PID that would cause integer overflow on Windows
        // This tests our fix for casting i32 to u32 without validation
        temp_file.write_all(b"-2147483648").unwrap(); // i32::MIN
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        // Should safely handle the negative PID and clean up the file
        assert_eq!(result, None);
        assert!(!std::path::Path::new(&path).exists());

        // Test Case 2: PID that exceeds platform limits
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write a PID that exceeds our validate_pid limits
        #[cfg(target_os = "linux")]
        let invalid_pid = "4194305"; // Just above Linux limit

        #[cfg(target_os = "macos")]
        let invalid_pid = "100000"; // Just above macOS limit

        #[cfg(target_os = "windows")]
        let invalid_pid = "4294967296"; // Just above u32::MAX (would overflow)

        #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
        let invalid_pid = "100000"; // Above conservative default

        temp_file.write_all(invalid_pid.as_bytes()).unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        // Should safely reject the invalid PID and clean up
        assert_eq!(result, None);
        assert!(!std::path::Path::new(&path).exists());

        // Test Case 3: Verify our own PID is correctly detected (positive test)
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        temp_file
            .write_all(std::process::id().to_string().as_bytes())
            .unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new_validated(&path).unwrap();
        let result = pidfile.get_owner().unwrap();
        // Should correctly identify our own process
        assert_eq!(result, Some(std::process::id() as i32));

        // Clean up
        std::fs::remove_file(&path).unwrap();
    }

    #[test]
    fn test_exists() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();

        // The temp file exists but we'll test with a different path
        let test_path = format!("{}.test", pid_path);
        let lock = Pidlock::new_validated(&test_path).unwrap();

        assert!(!lock.exists());

        // Create the file manually
        std::fs::write(&test_path, "1234").unwrap();

        // Now it should exist
        assert!(lock.exists());

        // Clean up
        std::fs::remove_file(&test_path).unwrap();
        assert!(!lock.exists());
    }

    #[test]
    fn test_is_active() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let test_path = format!("{}.test", pid_path);
        let lock = Pidlock::new_validated(&test_path).unwrap();

        // No lock file should return false
        assert!(!lock.is_active().unwrap());

        // Create lock file with our own PID
        std::fs::write(&test_path, std::process::id().to_string()).unwrap();

        // Should be active since our process is running
        assert!(lock.is_active().unwrap());

        // Create lock file with non-existent PID
        std::fs::write(&test_path, "999999").unwrap();

        // Should be inactive since PID doesn't exist
        assert!(!lock.is_active().unwrap());

        // Create lock file with invalid content
        std::fs::write(&test_path, "invalid").unwrap();

        // get_owner() will clean up invalid files and return Ok(None),
        // so is_active() should return Ok(false), not an error
        assert!(!lock.is_active().unwrap());

        // The invalid file should have been cleaned up
        assert!(!lock.exists());
    }

    #[test]
    fn test_check_stale_behavior() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let test_path = format!("{}.test", pid_path);
        let mut lock = Pidlock::new_validated(&test_path).unwrap();

        // No lock file means no stale lock
        assert!(!lock.exists());

        // Create a stale lock with non-existent PID
        std::fs::write(&test_path, "999999").unwrap();

        // Acquire should succeed by removing the stale lock
        assert!(lock.acquire().is_ok());
        assert!(lock.locked());

        // Clean up
        assert!(lock.release().is_ok());
    }

    #[test]
    fn test_drop_cleanup() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let test_path = format!("{}.test", pid_path);

        {
            let mut lock = Pidlock::new_validated(&test_path).unwrap();
            assert!(lock.acquire().is_ok());
            assert!(lock.exists());
            // Lock goes out of scope here and should be cleaned up
        }

        // File should be removed by Drop implementation
        assert!(!std::path::Path::new(&test_path).exists());
    }
}
