#![allow(clippy::print_stdout)]
//! Basic usage example for pidlock with type-safe state management
//!
//! This example demonstrates the new type-safe API that prevents invalid state
//! transitions at compile time. It also shows the basic workflow and error handling.

use pidlock::{AcquireError, New, Pidlock, Released};
use std::env;
use std::process;
use std::thread;
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Get the program name for the lock file
    let program_name = env::args()
        .next()
        .and_then(|path| {
            std::path::Path::new(&path)
                .file_stem()
                .and_then(|s| s.to_str())
                .map(|s| s.to_string())
        })
        .unwrap_or_else(|| "example_program".to_string());

    // Create lock file in system temp directory
    // NOTE: In production, consider using /var/run or /run/lock/ on Linux systems.
    let temp_dir = env::temp_dir();
    let lock_path = temp_dir.join(format!("{}.pid", program_name));

    println!("Attempting to acquire lock at: {:?}", lock_path);

    // Create a new lock - note the type is Pidlock<New>
    let lock: Pidlock<New> = Pidlock::new(&lock_path)?;
    println!("Lock created in New state");

    match lock.acquire() {
        Ok(acquired_lock) => {
            println!(
                "✓ Lock acquired successfully! Process ID: {} (Type: Pidlock<Acquired>)",
                process::id()
            );

            // We can check that we're the owner
            if let Some(owner_pid) = acquired_lock.get_owner()? {
                println!("Lock is owned by PID: {}", owner_pid);
                assert_eq!(owner_pid, std::process::id() as i32);
            }

            println!("This program will run for 5 seconds...");

            // Simulate some work
            for i in 1..=5 {
                println!("Working... {}/5", i);
                thread::sleep(Duration::from_secs(1));
            }

            println!("Work completed! Releasing lock...");

            // Release the lock - type changes to Pidlock<Released>
            let released_lock: Pidlock<Released> = acquired_lock.release()?;
            println!("✓ Lock released successfully (Type: Pidlock<Released>)");

            // Verify the lock file is gone
            assert!(!released_lock.exists());
            println!("Lock file has been removed");

            // Type Safety Demonstration:
            // These would not compile - invalid state transitions:
            // let reacquired = released_lock.acquire(); // Compile error! Cannot acquire from Released state
            // let re_released = released_lock.release(); // Compile error! Cannot release from Released state
            // let bad_release = lock.release(); // Compile error! `lock` was moved in acquire()
            // let bad_check = acquired_lock.exists(); // Compile error! `acquired_lock` was moved in release()

            println!("✓ Type safety: Invalid operations prevented at compile time!")
        }
        Err(AcquireError::LockExists) => {
            println!("✗ Another instance is already running!");

            // Try to get information about the existing lock
            // Note: we need to create another lock instance to check status
            let check_lock: Pidlock<New> = Pidlock::new(&lock_path)?;
            match check_lock.get_owner()? {
                Some(pid) => {
                    println!("  Existing lock is held by process ID: {}", pid);
                    match check_lock.is_active()? {
                        true => println!("  The process is still active"),
                        false => println!("  The process appears to be dead (stale lock)"),
                    }
                }
                None => println!("  No valid owner found for the lock file"),
            }

            process::exit(1);
        }
        Err(e) => {
            eprintln!("✗ Failed to acquire lock: {}", e);
            process::exit(1);
        }
    }

    println!("Example completed successfully!");
    Ok(())
}
