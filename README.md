# lockmap

[![Rust](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml/badge.svg)](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml)
[![codecov](https://codecov.io/gh/SF-Zhou/lockmap/graph/badge.svg?token=7U9JFC64U4)](https://codecov.io/gh/SF-Zhou/lockmap)
[![Crates.io](https://img.shields.io/crates/v/lockmap.svg)](https://crates.io/crates/lockmap)
[![Documentation](https://docs.rs/lockmap/badge.svg)](https://docs.rs/lockmap)
[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=shield)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_shield)

A high-performance, thread-safe HashMap implementation for Rust that provides fine-grained locking at the key level.

## Usage

```rust
use lockmap::LockMap;

// Create a new lock map
let map = LockMap::<String, String>::new();

// Set a value
map.insert_by_ref("key", "value".into());

// Get a value
assert_eq!(map.get("key"), Some("value".into()));

// Use entry API for exclusive access
{
    let mut entry = map.entry_by_ref("key");
    assert_eq!(entry.get().as_deref(), Some("value"));
    entry.insert("new value".to_string());
}

// Remove a value
assert_eq!(map.remove("key"), Some("new value".into()));
```


## License
[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_large)