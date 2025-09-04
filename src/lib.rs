use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::{fs, process};

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

/// Check whether a process exists, used to determine whether a pid file is stale.
///
/// # Safety
///
/// This function uses unsafe methods to determine process existence. The function
/// itself is private, and the input is validated prior to call.
fn process_exists(pid: i32) -> bool {
    // SAFETY: This function validates the input and return values before
    // continuing.
    #[cfg(target_os = "windows")]
    unsafe {
        // If GetExitCodeProcess returns STILL_ACTIVE, then the process
        // doesn't have an exit code (...or exited with code 259)
        use windows_sys::Win32::{
            Foundation::{CloseHandle, INVALID_HANDLE_VALUE, STILL_ACTIVE},
            System::Threading::{GetExitCodeProcess, OpenProcess, PROCESS_QUERY_INFORMATION},
        };
        let handle = OpenProcess(PROCESS_QUERY_INFORMATION, 0, pid as u32);

        // SAFETY: We must check if OpenProcess failed before using the handle
        if handle == 0 || handle == INVALID_HANDLE_VALUE {
            // Process doesn't exist or we don't have permission to query it
            return false;
        }

        let mut code = 0;
        let success = GetExitCodeProcess(handle, &mut code);
        CloseHandle(handle);

        // SAFETY: Only return true if GetExitCodeProcess succeeded and process is still active
        success != 0 && code == STILL_ACTIVE as u32
    }

    // SAFETY: This function is safe because it only checks for the existence
    // of a process
    #[cfg(not(target_os = "windows"))]
    unsafe {
        // From the POSIX standard: If sig is 0 (the null signal), error checking
        // is performed but no signal is actually sent. The null signal can be
        // used to check the validity of pid.
        let result = libc::kill(pid, 0);
        result == 0
    }
}

/// A pid-centered lock. A lock is considered "acquired" when a file exists on disk
/// at the path specified, containing the process id of the locking process.
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
    pub fn new(path: impl AsRef<Path>) -> Self {
        Pidlock {
            pid: process::id(),
            path: path.as_ref().into(),
            state: PidlockState::New,
        }
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

        let mut file = match fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&self.path)
        {
            Ok(file) => file,
            Err(_) => {
                return Err(PidlockError::LockExists);
            }
        };
        file.write_all(&self.pid.to_string().into_bytes()[..])
            .map_err(PidlockError::from)?;

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
            warn!(
                "Removing corrupted/invalid pid file at {}",
                self.path.to_str().unwrap_or("<invalid>")
            );
            fs::remove_file(&self.path).map_err(PidlockError::from)?;
            return Ok(None);
        }

        match contents.trim().parse::<i32>() {
            Ok(pid) if process_exists(pid) => Ok(Some(pid)),
            Ok(_) => {
                warn!(
                    "Removing stale pid file at {}",
                    self.path.to_str().unwrap_or("<invalid>")
                );
                fs::remove_file(&self.path).map_err(PidlockError::from)?;
                Ok(None)
            }
            Err(_) => {
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
}
