extern crate libc;
#[macro_use]
extern crate log;
#[cfg(test)]
extern crate rand;

use std::io::{Read, Write};
use std::{fs, process};

/// Errors that may occur during the `Pidlock` lifetime.
#[derive(Debug, PartialEq)]
pub enum PidlockError {
    #[doc = "A lock already exists"]
    LockExists,
    #[doc = "An operation was attempted in the wrong state, e.g. releasing before acquiring."]
    InvalidState,
}

/// A result from a Pidlock operation
type PidlockResult = Result<Pidlock, PidlockError>;

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
    // From the POSIX standard: If sig is 0 (the null signal), error checking
    // is performed but no signal is actually sent. The null signal can be
    // used to check the validity of pid.
    unsafe {
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
    path: String,
    #[doc = "Current state of the Pidlock"]
    state: PidlockState,
}

impl Pidlock {
    /// Create a new Pidlock at the provided path.
    pub fn new(path: &str) -> Self {
        Pidlock {
            pid: process::id(),
            path: path.to_string(),
            state: PidlockState::New,
        }
    }

    /// Check whether a lock file already exists, and if it does, whether the
    /// specified pid is still a valid process id on the system.
    fn check_stale(&self) {
        if let Ok(mut file) = fs::OpenOptions::new().read(true).open(self.path.clone()) {
            let mut contents = String::new();
            file.read_to_string(&mut contents).unwrap();

            match contents.trim().parse::<i32>() {
                Ok(pid) => {
                    if !process_exists(pid) {
                        warn!("Removing stale pid file at {}", self.path);
                        fs::remove_file(&self.path).unwrap();
                    }
                }
                Err(_) => {
                    warn!("Corrupted/invalid pid file at {}", self.path);
                    fs::remove_file(&self.path).unwrap();
                }
            }
        }
    }

    /// Acquire a lock.
    pub fn acquire(self) -> PidlockResult {
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
            .open(self.path.clone())
        {
            Ok(file) => file,
            Err(_) => {
                return Err(PidlockError::LockExists);
            }
        };
        file.write_all(&format!("{}", self.pid).into_bytes()[..])
            .unwrap();

        Ok(Pidlock {
            pid: self.pid,
            path: self.path,
            state: PidlockState::Acquired,
        })
    }

    /// Returns true when the lock is in an acquired state.
    pub fn locked(&self) -> bool {
        self.state == PidlockState::Acquired
    }

    /// Release the lock.
    pub fn release(self) -> PidlockResult {
        match self.state {
            PidlockState::Acquired => {}
            _ => {
                return Err(PidlockError::InvalidState);
            }
        }

        fs::remove_file(self.path.clone()).unwrap();

        Ok(Pidlock {
            pid: self.pid,
            path: self.path,
            state: PidlockState::Released,
        })
    }
}

#[cfg(test)]
mod tests {
    use rand::distributions::Alphanumeric;
    use rand::{thread_rng, Rng};

    use super::PidlockState;
    use super::{Pidlock, PidlockError};

    // This was removed from the library itself, but retained here
    // to assert backwards compatibility with std::process::id
    fn getpid() -> u32 {
        unsafe { libc::getpid() as u32 }
    }

    fn make_pid_path() -> String {
        let rand_string: String = thread_rng()
            .sample_iter(&Alphanumeric)
            .take(10)
            .map(char::from)
            .collect();
        format!("/tmp/test.{}.pid", rand_string).to_string()
    }

    #[test]
    fn test_new() {
        let pid_path = make_pid_path();
        let pidfile = Pidlock::new(&pid_path);

        assert_eq!(pidfile.pid, getpid());
        assert_eq!(pidfile.path, pid_path);
        assert_eq!(pidfile.state, PidlockState::New);
    }

    #[test]
    fn test_acquire_and_release() {
        let pidfile = Pidlock::new(&make_pid_path()).acquire().unwrap();

        assert_eq!(pidfile.state, PidlockState::Acquired);

        let pidfile = pidfile.release().unwrap();

        assert_eq!(pidfile.state, PidlockState::Released);
    }

    #[test]
    fn test_acquire_lock_exists() {
        let orig_pidfile = Pidlock::new(&make_pid_path()).acquire().unwrap();

        let pidfile = Pidlock::new(&orig_pidfile.path);
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
        let pidfile = Pidlock::new(&make_pid_path()).acquire().unwrap();
        match pidfile.acquire() {
            Err(err) => {
                // XXX: rockstar (19 Jan 2021) - The pid file doesn't get
                // removed here as pidfile was consumed, so we can't call
                // pidfile.release().
                assert_eq!(err, PidlockError::InvalidState);
            }
            Ok(pidfile) => {
                pidfile.release().unwrap();
                panic!("Test failed");
            }
        }
    }

    #[test]
    fn test_release_bad_state() {
        let pidfile = Pidlock::new(&make_pid_path());
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
        let pidfile = Pidlock::new(&make_pid_path()).acquire().unwrap();
        assert!(pidfile.locked());
    }

    #[test]
    fn test_locked_not_locked() {
        let pidfile = Pidlock::new(&make_pid_path());
        assert!(!pidfile.locked());
    }
}
