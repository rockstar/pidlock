#![allow(clippy::print_stdout)]
//! Advanced usage example showing error handling and lock inspection
//!
//! This example demonstrates more sophisticated lock management including
//! error handling, lock status checking, and graceful handling of stale locks.

use pidlock::{AcquireError, Acquired, InvalidPathError, New, NewError, Pidlock, Released};
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
        "conversions" => demonstrate_type_conversions(),
        _ => {
            eprintln!("Usage: {} [run|check|cleanup|conversions]", args[0]);
            eprintln!("  run         - Run the program with lock protection");
            eprintln!("  check       - Check the status of existing locks");
            eprintln!("  cleanup     - Clean up any stale lock files");
            eprintln!("  conversions - Demonstrate type conversion patterns");
            process::exit(1);
        }
    }
}

fn run_with_lock() -> Result<(), Box<dyn std::error::Error>> {
    let lock_path = get_lock_path()?;

    println!("Creating lock at: {:?}", lock_path);

    let lock = match Pidlock::new(&lock_path) {
        Ok(lock) => lock,
        Err(NewError::InvalidPath(InvalidPathError::EmptyPath)) => {
            eprintln!("Error: Lock path cannot be empty");
            process::exit(1);
        }
        Err(NewError::InvalidPath(InvalidPathError::ProblematicCharacter {
            character,
            filename,
        })) => {
            eprintln!(
                "Error: Invalid character '{}' in filename: {}",
                character, filename
            );
            process::exit(1);
        }
        Err(NewError::InvalidPath(InvalidPathError::ReservedName { filename })) => {
            eprintln!("Error: '{}' is a reserved filename on Windows", filename);
            process::exit(1);
        }
        Err(e) => {
            eprintln!("Error creating lock: {}", e);
            process::exit(1);
        }
    };

    match lock.acquire() {
        Ok(acquired_lock) => {
            println!("✓ Lock acquired successfully!");
            simulate_work()?;
            let released_lock = acquired_lock.release()?;
            println!("✓ Lock released successfully");
            // We could use released_lock here if needed, but dropping it is fine
            drop(released_lock);
        }
        Err(AcquireError::LockExists) => {
            println!("✗ Lock already exists");
            // Create a new lock instance for inspection since the original was consumed
            let inspection_lock = Pidlock::new(&lock_path)?;
            handle_existing_lock(&inspection_lock)?;
            process::exit(1);
        }
        Err(AcquireError::IOError(io_err)) => {
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
    let lock = Pidlock::new(&lock_path)?;

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
    let lock = Pidlock::new(&lock_path)?;

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

fn demonstrate_type_conversions() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Type Conversion Demonstrations ===");

    let lock_path = get_lock_path()?;

    // Create a new lock - explicit type annotation shows the state
    let new_lock: Pidlock<New> = Pidlock::new(&lock_path)?;
    println!("✓ Created Pidlock<New>");

    // Standard workflow with explicit type annotations
    println!("Converting Pidlock<New> -> Pidlock<Acquired> via acquire()...");
    let acquired_lock: Pidlock<Acquired> = new_lock.acquire()?;
    println!("✓ Conversion successful - now have Pidlock<Acquired>");

    // Check that we're the owner
    if let Some(owner_pid) = acquired_lock.get_owner()? {
        println!("  Lock is owned by PID: {}", owner_pid);
        assert_eq!(owner_pid, std::process::id() as i32);
    }

    println!("Converting Pidlock<Acquired> -> Pidlock<Released> via release()...");
    let released_lock: Pidlock<Released> = acquired_lock.release()?;
    println!("✓ Conversion successful - now have Pidlock<Released>");

    // Verify final state
    assert!(!released_lock.exists());
    println!("✓ Lock file properly removed during release");

    println!("\n=== Type Safety Guarantees ===");
    println!("The following operations would cause COMPILE-TIME errors:");
    println!("  // released_lock.acquire() - Cannot acquire from Released state");
    println!("  // released_lock.release() - Cannot release from Released state");
    println!("  // new_lock.release() - Cannot release from New state");
    println!("  // new_lock.exists() - Cannot use moved value after acquire()");
    println!("✓ Type system prevents invalid state transitions!");

    Ok(())
}

fn handle_existing_lock(lock: &Pidlock<New>) -> Result<(), Box<dyn std::error::Error>> {
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
