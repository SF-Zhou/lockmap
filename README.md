# lockmap

[![Rust](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml/badge.svg)](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml)
[![codecov](https://codecov.io/gh/SF-Zhou/lockmap/graph/badge.svg?token=7U9JFC64U4)](https://codecov.io/gh/SF-Zhou/lockmap)
[![Crates.io](https://img.shields.io/crates/v/lockmap.svg)](https://crates.io/crates/lockmap)
[![Documentation](https://docs.rs/lockmap/badge.svg)](https://docs.rs/lockmap)

A high-performance, thread-safe HashMap implementation for Rust that provides fine-grained locking at the key level.

## Usage

```rust
use lockmap::LockMap;

// Create a new lock map
let map = LockMap::new();

// Set a value
map.set("key", "value");

// Get a value
assert_eq!(map.get("key"), Some("value"));

// Use entry API for exclusive access
{
    let entry = map.entry("key");
    *entry.value = Some("new value");
}

// Remove a value
map.remove("key");
```
