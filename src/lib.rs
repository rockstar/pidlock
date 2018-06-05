extern crate libc;
#[macro_use]
extern crate log;

use std::fs;
use std::io::{Read, Write};

#[derive(Debug, PartialEq)]
pub enum PidlockError {
    LockExists,
    InvalidState,
}

type PidlockResult = Result<(), PidlockError>;

#[derive(Debug, PartialEq)]
enum PidlockState {
    New,
    Acquired,
    Released,
}

fn getpid() -> u32 {
    unsafe { libc::getpid() as u32 }
}

fn process_exists(pid: i32) -> bool {
    // From the POSIX standard: If sig is 0 (the null signal), error checking
    // is performed but no signal is actually sent. The null signal can be
    // used to check the validity of pid.
    unsafe {
        let result = libc::kill(pid, 0);
        result == 0
    }
}

pub struct Pidlock {
    pid: u32,
    path: String,
    state: PidlockState,
}

impl Pidlock {
    pub fn new(path: &str) -> Self {
        Pidlock {
            pid: getpid(),
            path: path.to_string(),
            state: PidlockState::New,
        }
    }

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
                Err(_) => fs::remove_file(&self.path).unwrap(),
            }
        }
    }

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
            .open(self.path.clone())
        {
            Ok(file) => file,
            Err(_) => {
                return Err(PidlockError::LockExists);
            }
        };
        file.write_all(&format!("{}", self.pid).into_bytes()[..])
            .unwrap();

        self.state = PidlockState::Acquired;
        Ok(())
    }

    pub fn release(&mut self) -> PidlockResult {
        match self.state {
            PidlockState::Acquired => {}
            _ => {
                return Err(PidlockError::InvalidState);
            }
        }

        fs::remove_file(self.path.clone()).unwrap();

        self.state = PidlockState::Released;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{Pidlock, PidlockError};
    use super::{getpid, PidlockState};

    const TEST_PID: &str = "/tmp/test.pid";

    #[test]
    fn test_new() {
        let pidfile = Pidlock::new(TEST_PID);

        assert_eq!(pidfile.pid, getpid());
        assert_eq!(pidfile.path, "/tmp/test.pid".to_string());
        assert_eq!(pidfile.state, PidlockState::New);
    }

    #[test]
    fn test_acquire_and_release() {
        let mut pidfile = Pidlock::new(TEST_PID);
        pidfile.acquire().unwrap();

        assert_eq!(pidfile.state, PidlockState::Acquired);

        pidfile.release().unwrap();

        assert_eq!(pidfile.state, PidlockState::Released);
    }

    #[test]
    fn test_acquire_lock_exists() {
        let mut orig_pidfile = Pidlock::new(TEST_PID);
        orig_pidfile.acquire().unwrap();

        let mut pidfile = Pidlock::new(TEST_PID);
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
        let mut pidfile = Pidlock::new(TEST_PID);
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
        let mut pidfile = Pidlock::new(TEST_PID);
        match pidfile.release() {
            Err(err) => {
                assert_eq!(err, PidlockError::InvalidState);
            }
            _ => {
                panic!("Test failed");
            }
        }
    }
}
