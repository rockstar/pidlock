#![allow(clippy::print_stdout)]
//! Advanced usage example showing error handling and lock inspection
//!
//! This example demonstrates more sophisticated lock management including
//! error handling, lock status checking, and graceful handling of stale locks.

use pidlock::{InvalidPathError, Pidlock, PidlockError};
use std::env;
use std::process;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Parse command line arguments
    let args: Vec<String> = env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("run");

    match mode {
        "run" => run_with_lock(),
        "check" => check_lock_status(),
        "cleanup" => cleanup_stale_locks(),
        _ => {
            eprintln!("Usage: {} [run|check|cleanup]", args[0]);
            eprintln!("  run     - Run the program with lock protection");
            eprintln!("  check   - Check the status of existing locks");
            eprintln!("  cleanup - Clean up any stale lock files");
            process::exit(1);
        }
    }
}

fn run_with_lock() -> Result<(), Box<dyn std::error::Error>> {
    let lock_path = get_lock_path()?;

    println!("Creating lock at: {:?}", lock_path);

    let mut lock = match Pidlock::new_validated(&lock_path) {
        Ok(lock) => lock,
        Err(PidlockError::InvalidPath(InvalidPathError::EmptyPath)) => {
            eprintln!("Error: Lock path cannot be empty");
            process::exit(1);
        }
        Err(PidlockError::InvalidPath(InvalidPathError::ProblematicCharacter {
            character,
            filename,
        })) => {
            eprintln!(
                "Error: Invalid character '{}' in filename: {}",
                character, filename
            );
            process::exit(1);
        }
        Err(PidlockError::InvalidPath(InvalidPathError::ReservedName { filename })) => {
            eprintln!("Error: '{}' is a reserved filename on Windows", filename);
            process::exit(1);
        }
        Err(e) => {
            eprintln!("Error creating lock: {}", e);
            process::exit(1);
        }
    };

    match lock.acquire() {
        Ok(()) => {
            println!("✓ Lock acquired successfully!");
            simulate_work()?;
            lock.release()?;
            println!("✓ Lock released successfully");
        }
        Err(PidlockError::LockExists) => {
            println!("✗ Lock already exists");
            handle_existing_lock(&lock)?;
            process::exit(1);
        }
        Err(PidlockError::IOError(io_err)) => {
            eprintln!("✗ I/O error while acquiring lock: {}", io_err);
            process::exit(1);
        }
        Err(e) => {
            eprintln!("✗ Unexpected error: {}", e);
            process::exit(1);
        }
    }

    Ok(())
}

fn check_lock_status() -> Result<(), Box<dyn std::error::Error>> {
    let lock_path = get_lock_path()?;
    let lock = Pidlock::new_validated(&lock_path)?;

    println!("Checking lock status at: {:?}", lock_path);

    if !lock.exists() {
        println!("✓ No lock file exists");
        return Ok(());
    }

    println!("📁 Lock file exists");

    match lock.get_owner()? {
        Some(pid) => {
            println!("🔍 Lock is owned by PID: {}", pid);

            match lock.is_active()? {
                true => {
                    println!("✅ Process is active - lock is valid");
                }
                false => {
                    println!("💀 Process is dead - lock is stale");
                }
            }
        }
        None => {
            println!("❌ Lock file exists but no valid owner found (probably cleaned up)");
        }
    }

    Ok(())
}

fn cleanup_stale_locks() -> Result<(), Box<dyn std::error::Error>> {
    let lock_path = get_lock_path()?;
    let lock = Pidlock::new_validated(&lock_path)?;

    println!("Checking for stale locks at: {:?}", lock_path);

    if !lock.exists() {
        println!("✓ No lock file to clean up");
        return Ok(());
    }

    match lock.is_active()? {
        true => {
            println!("⚠️  Lock is held by an active process - not cleaning up");
            if let Some(pid) = lock.get_owner()? {
                println!("   Active PID: {}", pid);
            }
        }
        false => {
            println!("🧹 Found stale lock, cleaning up...");
            // Note: In a real implementation, you might want to be more careful
            // about removing lock files, perhaps requiring additional confirmation
            std::fs::remove_file(&lock_path)?;
            println!("✓ Stale lock removed");
        }
    }

    Ok(())
}

fn handle_existing_lock(lock: &Pidlock) -> Result<(), Box<dyn std::error::Error>> {
    match lock.get_owner()? {
        Some(pid) => {
            println!("  Lock is held by PID: {}", pid);

            match lock.is_active()? {
                true => {
                    println!("  Process is still running");
                    println!("  You may need to wait or stop the other instance");
                }
                false => {
                    println!("  Process appears to be dead (stale lock)");
                    println!("  You can try running with 'cleanup' mode to remove stale locks");
                }
            }
        }
        None => {
            println!("  No valid owner found (lock may have been cleaned up)");
        }
    }
    Ok(())
}

fn simulate_work() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔧 Starting work simulation...");

    let start_time = SystemTime::now();

    for i in 1..=5 {
        println!("  Step {}/5: Processing...", i);
        std::thread::sleep(Duration::from_secs(1));
    }

    let duration = start_time.elapsed()?;
    println!("✅ Work completed in {:.2}s", duration.as_secs_f64());

    Ok(())
}

fn get_lock_path() -> Result<std::path::PathBuf, Box<dyn std::error::Error>> {
    // NOTE: This example uses temp_dir() for portability and safety.
    // In production, consider using /var/run or /run/lock/ on Linux systems.
    let temp_dir = env::temp_dir();
    let timestamp = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs();

    // Use a timestamp to avoid conflicts when running multiple examples
    let lock_name = format!("pidlock_advanced_example_{}.pid", timestamp % 10000);
    Ok(temp_dir.join(lock_name))
}
