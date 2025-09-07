#![allow(clippy::print_stdout)]
//! Basic usage example for pidlock
//!
//! This example demonstrates the most common use case: ensuring only one instance
//! of a program runs at a time.

use pidlock::{Pidlock, PidlockError};
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
    let temp_dir = env::temp_dir();
    let lock_path = temp_dir.join(format!("{}.pid", program_name));

    println!("Attempting to acquire lock at: {:?}", lock_path);

    // Create and try to acquire the lock
    let mut lock = Pidlock::new_validated(&lock_path)?;

    match lock.acquire() {
        Ok(()) => {
            println!(
                "✓ Lock acquired successfully! Process ID: {}",
                process::id()
            );
            println!("This program will run for 10 seconds...");

            // Simulate some work
            for i in 1..=10 {
                println!("Working... {}/10", i);
                thread::sleep(Duration::from_secs(1));
            }

            println!("Work completed! Releasing lock...");
            lock.release()?;
            println!("✓ Lock released successfully");
        }
        Err(PidlockError::LockExists) => {
            println!("✗ Another instance is already running!");

            // Try to get information about the existing lock
            match lock.get_owner()? {
                Some(pid) => {
                    println!("  Existing lock is held by process ID: {}", pid);
                    match lock.is_active()? {
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

    Ok(())
}
