# pidlock

A library for creating and managing PID-based file locks, providing a simple and reliable way to ensure only one instance of a program runs at a time.

[![Crates.io](https://img.shields.io/crates/v/pidlock.svg)](https://crates.io/crates/pidlock)
[![Documentation](https://docs.rs/pidlock/badge.svg)](https://docs.rs/pidlock)
[![CI](https://github.com/rockstar/pidlock/workflows/Perform%20checks/badge.svg)](https://github.com/rockstar/pidlock/actions)

## Features

- **Cross-platform**: Works on Unix-like systems and Windows
- **Stale lock detection**: Automatically detects and cleans up locks from dead processes
- **Path validation**: Ensures lock file paths are valid across platforms
- **Safe cleanup**: Automatically releases locks when the `Pidlock` is dropped
- **Comprehensive error handling**: Detailed error types for different failure scenarios
- **Type-safe state management**: Compile-time prevention of invalid state transitions

## Quick Start

Add this to your `Cargo.toml`:

```toml
[dependencies]
pidlock = "0.2"
```

## Type-Safe Usage (Recommended)

Starting with version 0.2.0, pidlock uses Rust's type system to prevent invalid state transitions at compile time:

```rust
use pidlock::{Pidlock, New, Acquired, Released, AcquireError};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create a new lock - starts in New state
    let lock: Pidlock<New> = Pidlock::new("/run/lock/my_app.pid")?;

    // Try to acquire the lock - transitions to Acquired state
    match lock.acquire() {
        Ok(acquired_lock) => {
            println!("Lock acquired successfully!");
            
            // Do your work here...
            
            // Release the lock - transitions to Released state
            let _released_lock: Pidlock<Released> = acquired_lock.release()?;
            println!("Lock released successfully!");
        }
        Err(AcquireError::LockExists) => {
            println!("Another instance is already running");
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("Failed to acquire lock: {}", e);
            std::process::exit(1);
        }
    }
    
    Ok(())
}
```

### Compile-Time Safety

The type system prevents common mistakes:

```rust
use pidlock::{Pidlock, New, Acquired, Released};

// This won't compile - cannot acquire from Released state:
// let released_lock: Pidlock<Released> = // ...
// let reacquired = released_lock.acquire(); // ERROR!

// This won't compile - cannot release from New state:  
// let lock: Pidlock<New> = // ...
// let released = lock.release(); // ERROR!

// This won't compile - cannot use moved value:
// let lock: Pidlock<New> = // ...
// let acquired = lock.acquire()?;
// println!("{}", lock.exists()); // ERROR! lock was moved
```
            std::process::exit(1);
        }
    }
    
    Ok(())
}
```

## Advanced Usage

### Checking Lock Status

```rust
use pidlock::Pidlock;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let lock = Pidlock::new("/run/lock/my_app.pid")?;

    // Check if a lock file exists
    if lock.exists() {
        // Check if the lock is held by an active process
        match lock.is_active()? {
            true => println!("Lock is held by an active process"),
            false => println!("Lock file exists but process is dead (stale lock)"),
        }
    } else {
        println!("No lock file exists");
    }
    
    Ok(())
}
```

### Error Handling

```rust
use pidlock::{Pidlock, NewError, InvalidPathError};

fn main() {
    let result = Pidlock::new("invalid<path>");
    match result {
        Ok(_) => println!("Path is valid"),
        Err(NewError::InvalidPath(InvalidPathError::ProblematicCharacter { character, filename })) => {
            println!("Invalid character '{}' in filename: {}", character, filename);
        }
        Err(e) => println!("Other error: {}", e),
    }
}
```

### Safe Cleanup with RAII

```rust
use pidlock::Pidlock;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    {
        let lock = Pidlock::new("/run/lock/my_app.pid")?;
        let acquired_lock = lock.acquire()?;
        
        // Do work here...
        // Lock is automatically released when it goes out of scope
    }
    
    // Lock file is now cleaned up
    Ok(())
}
```

## Migration from 0.1.x

If you're upgrading from version 0.1.x:

- Replace `Pidlock::new()` with `Pidlock::new()` (no change needed for the method name)
- The API now uses specific error types (`NewError`, `AcquireError`, etc.) instead of a unified `PidlockError`
- Consider the improved type-safe state management for better compile-time safety

```rust
// Old (0.1.x)
let mut lock = pidlock::Pidlock::new("/path/to/pidfile.pid");

// New (0.2.x)
let lock = pidlock::Pidlock::new("/path/to/pidfile.pid")?;
let acquired_lock = lock.acquire()?;
```

## Platform Considerations

- **Unix/Linux**: Uses POSIX signals for process detection, respects umask for permissions
- **Windows**: Uses Win32 APIs for process detection, handles reserved filenames
- **File permissions**: Lock files are created with restrictive permissions (600 on Unix)
- **Path validation**: Automatically validates paths for cross-platform compatibility

## Safety

This library uses unsafe code for platform-specific process detection, but all unsafe operations are carefully validated and documented. The library ensures that:

- PID values are validated before use in system calls
- Windows handles are properly managed and cleaned up
- Unix signals are used safely without affecting target processes

## License

pidlock is licensed under the MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
