use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::{fs, process};

#[cfg(feature = "log")]
use log::warn;

/// Errors that may occur during the `Pidlock` lifetime.
#[non_exhaustive]
#[derive(Debug)]
pub enum PidlockError {
    #[doc = "A lock already exists"]
    LockExists,
    #[doc = "An operation was attempted in the wrong state, e.g. releasing before acquiring."]
    InvalidState,
    #[doc = "An I/O error occurred"]
    IOError(std::io::Error),
    #[doc = "Invalid path provided for lock file"]
    InvalidPath(String),
}

impl PartialEq for PidlockError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PidlockError::LockExists, PidlockError::LockExists) => true,
            (PidlockError::InvalidState, PidlockError::InvalidState) => true,
            (PidlockError::IOError(a), PidlockError::IOError(b)) => {
                // Compare IO errors by their kind and to_string representation
                a.kind() == b.kind() && a.to_string() == b.to_string()
            }
            (PidlockError::InvalidPath(a), PidlockError::InvalidPath(b)) => a == b,
            _ => false,
        }
    }
}

impl From<std::io::Error> for PidlockError {
    fn from(err: std::io::Error) -> Self {
        PidlockError::IOError(err)
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
        return Err(PidlockError::InvalidPath(
            "Path cannot be empty".to_string(),
        ));
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
                return Err(PidlockError::InvalidPath(format!(
                    "Filename '{}' is reserved on Windows",
                    filename_str
                )));
            }
        }

        // Check for problematic characters
        let problematic_chars = ['<', '>', ':', '"', '|', '?', '*'];
        for &ch in &problematic_chars {
            if filename_str.contains(ch) {
                return Err(PidlockError::InvalidPath(format!(
                    "Filename contains problematic character '{}': {}",
                    ch, filename_str
                )));
            }
        }

        // Check for control characters
        if filename_str.chars().any(|c| c.is_control()) {
            return Err(PidlockError::InvalidPath(format!(
                "Filename contains control characters: {}",
                filename_str
            )));
        }
    }

    // Try to validate parent directory exists or can be created
    if let Some(parent) = path.parent()
        && !parent.exists()
    {
        // Check if we can potentially create the directory
        if let Err(e) = fs::create_dir_all(parent) {
            return Err(PidlockError::InvalidPath(format!(
                "Cannot create parent directory {}: {}",
                parent.display(),
                e
            )));
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
        // Linux typically allows PIDs up to 2^22 (4194304) by default
        // But can be configured higher. We'll use a conservative limit.
        pid <= 4194304
    }

    #[cfg(target_os = "macos")]
    {
        // macOS uses 32-bit PIDs but typically keeps them much lower
        pid <= 99999
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
        // SAFETY: We use Windows APIs according to their documented contracts:
        // - OpenProcess is called with valid flags and a validated positive PID
        // - We check return values before using handles
        // - CloseHandle is always called to prevent resource leaks
        // - GetExitCodeProcess is only called with a valid handle
        // The PID has already been validated by validate_pid() to be positive and within range
        unsafe {
            use windows_sys::Win32::{
                Foundation::{CloseHandle, INVALID_HANDLE_VALUE, STILL_ACTIVE},
                System::Threading::{GetExitCodeProcess, OpenProcess, PROCESS_QUERY_INFORMATION},
            };

            let handle = OpenProcess(PROCESS_QUERY_INFORMATION, 0, pid as u32);

            // Check if OpenProcess failed (returns 0 or INVALID_HANDLE_VALUE)
            if handle == 0 || handle == INVALID_HANDLE_VALUE {
                // Process doesn't exist or we don't have permission to query it
                return false;
            }

            // Use RAII-style cleanup to ensure handle is always closed, even on panic
            struct HandleGuard(isize);
            impl Drop for HandleGuard {
                fn drop(&mut self) {
                    // SAFETY: We only create HandleGuard with valid handles from OpenProcess
                    unsafe {
                        CloseHandle(self.0);
                    }
                }
            }
            let _guard = HandleGuard(handle);

            let mut exit_code = 0;
            let success = GetExitCodeProcess(handle, &mut exit_code);

            // Return true only if GetExitCodeProcess succeeded AND process is still active
            // Note: STILL_ACTIVE (259) could theoretically be a real exit code, but it's
            // extremely unlikely in practice. This is the documented Windows API pattern
            // for checking if a process is still running. The risk of false positives
            // (a process that actually exited with code 259) is negligible.
            success != 0 && exit_code as i32 == STILL_ACTIVE
        }
    }

    #[cfg(not(target_os = "windows"))]
    {
        // SAFETY: libc::kill with signal 0 is safe when called with a valid PID because:
        // - Signal 0 (null signal) performs no actual signal delivery
        // - It only checks if the process exists and we have permission to signal it
        // - POSIX guarantees this is a safe operation that won't affect the target process
        // - We've already validated the PID is within reasonable bounds
        unsafe {
            let result = libc::kill(pid, 0);
            result == 0
        }
    }
}

/// A pid-centered lock. A lock is considered "acquired" when a file exists on disk
/// at the path specified, containing the process id of the locking process.
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
    fn check_stale(&self) {
        let _ = self.get_owner();
    }

    /// Acquire a lock.
    pub fn acquire(&mut self) -> PidlockResult {
        match self.state {
            PidlockState::New => {}
            _ => {
                return Err(PidlockError::InvalidState);
            }
        }
        self.check_stale();

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
    pub fn locked(&self) -> bool {
        self.state == PidlockState::Acquired
    }

    /// Release the lock.
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

    /// Gets the owner of this lockfile, returning the pid. If the lock file doesn't exist,
    /// or the specified pid is not a valid process id on the system, it clears it.
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
    fn drop(&mut self) {
        if self.state == PidlockState::Acquired {
            // We use a best-effort approach here - if cleanup fails, we don't panic
            // because that could mask the original panic that triggered the drop.
            // We also don't log errors here to avoid potential issues during unwinding.
            let _ = fs::remove_file(&self.path);
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(deprecated)]
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
        let pidfile = Pidlock::new(pid_path);

        assert_eq!(pidfile.pid, std::process::id());
        assert_eq!(pidfile.path, PathBuf::from(pid_path));
        assert_eq!(pidfile.state, PidlockState::New);
    }

    #[test]
    fn test_acquire_and_release() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let mut pidfile = Pidlock::new(pid_path);
        pidfile.acquire().unwrap();

        assert_eq!(pidfile.state, PidlockState::Acquired);

        pidfile.release().unwrap();

        assert_eq!(pidfile.state, PidlockState::Released);
    }

    #[test]
    fn test_acquire_lock_exists() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let mut orig_pidfile = Pidlock::new(pid_path);
        orig_pidfile.acquire().unwrap();

        let mut pidfile = Pidlock::new(orig_pidfile.path.to_str().unwrap());
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
        let mut pidfile = Pidlock::new(pid_path);
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
        let mut pidfile = Pidlock::new(pid_path);
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
        let mut pidfile = Pidlock::new(pid_path);
        pidfile.acquire().unwrap();
        assert!(pidfile.locked());
    }

    #[test]
    fn test_locked_not_locked() {
        let temp_file = make_temp_file();
        let pid_path = temp_file.path().to_str().unwrap();
        let pidfile = Pidlock::new(pid_path);
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

        let mut pidfile = Pidlock::new(&path);
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

        let mut pidfile = Pidlock::new(&path);
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

        let mut pidfile = Pidlock::new(&path);
        pidfile.acquire().unwrap();
        assert_eq!(pidfile.state, PidlockState::Acquired);
    }

    #[test]
    fn test_drop_cleans_up_lock_file() {
        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Create and acquire a lock in a scope
        {
            let mut pidfile = Pidlock::new(&path);
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
            let _pidfile = Pidlock::new(&path);
            // Lock is not acquired, so drop should not try to remove anything
        }

        // Should not have attempted to remove a non-existent lock file
        // (This test mainly ensures no panic occurs during drop)

        // Now create a lock, acquire and manually release it
        {
            let mut pidfile = Pidlock::new(&path);
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

        let pidfile = Pidlock::new(&path);
        let result = pidfile.get_owner().unwrap();
        assert_eq!(result, None);
    }

    #[test]
    fn test_get_owner_valid_pid() {
        let temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // First create a lock with our own PID
        let mut pidfile = Pidlock::new(&path);
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

        let pidfile = Pidlock::new(&path);
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

        let pidfile = Pidlock::new(&path);
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

        let pidfile = Pidlock::new(&path);
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

        let pidfile = Pidlock::new(&path);
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

        let pidfile = Pidlock::new(&path);
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

        let pidfile = Pidlock::new(&path);
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
        let mut lock1 = Pidlock::new(&path);
        assert!(lock1.acquire().is_ok());

        // Second lock should fail with LockExists
        let mut lock2 = Pidlock::new(&path);
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
        let mut pidfile = Pidlock::new(&path);
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
            assert!(validate_pid(4194304)); // Should be valid on Linux
            assert!(!validate_pid(4194305)); // Should be invalid
        }

        #[cfg(target_os = "macos")]
        {
            assert!(validate_pid(99999)); // Should be valid on macOS
            assert!(!validate_pid(100000)); // Should be invalid
        }
    }

    #[test]
    fn test_get_owner_with_invalid_pid_range() {
        let mut temp_file = make_temp_file();
        let path = temp_file.path().to_string_lossy().to_string();

        // Write a PID that's outside valid range (negative)
        temp_file.write_all(b"-500").unwrap();
        temp_file.flush().unwrap();

        let pidfile = Pidlock::new(&path);
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

        let mut pidfile = Pidlock::new(&path);
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

        let mut pidfile = Pidlock::new(&path);
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
        let mut pidfile = Pidlock::new("/root/cannot_create_here/test.pid");

        let result = pidfile.acquire();
        match result {
            Ok(_) => {
                // This might actually succeed in some test environments
                // so we don't fail the test
            }
            Err(PidlockError::IOError(io_err)) => {
                // Verify we get detailed error information
                assert!(!io_err.to_string().is_empty());
                // Should be a permission denied or not found error
                assert!(matches!(
                    io_err.kind(),
                    std::io::ErrorKind::PermissionDenied | std::io::ErrorKind::NotFound
                ));
            }
            Err(other) => panic!("Expected IOError, got {:?}", other),
        }
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

        let pidfile = Pidlock::new(&path);
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

        let pidfile = Pidlock::new(&path);
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

        let pidfile = Pidlock::new(&path);
        let result = pidfile.get_owner().unwrap();
        // Should correctly identify our own process
        assert_eq!(result, Some(std::process::id() as i32));

        // Clean up
        std::fs::remove_file(&path).unwrap();
    }
}
