pidlock
==

A library for working with pidfiles, with a lock-like API.

Usage
--

```
extern crate pidlock;

fn main() {
    let mut lock = pidlock::Pidlock("/path/to/pidfile.pid");
    lock.acquire().unwrap();

    ...

    lock.release().unwrap();
}
```

License
--

pidlock is licensed under the MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
