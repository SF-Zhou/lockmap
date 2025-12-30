# lockmap

[![Rust](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml/badge.svg)](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml)
[![codecov](https://codecov.io/gh/SF-Zhou/lockmap/graph/badge.svg?token=7U9JFC64U4)](https://codecov.io/gh/SF-Zhou/lockmap)
[![Crates.io](https://img.shields.io/crates/v/lockmap.svg)](https://crates.io/crates/lockmap)
[![Documentation](https://docs.rs/lockmap/badge.svg)](https://docs.rs/lockmap)
[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=shield)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_shield)

**LockMap** is a high-performance, thread-safe HashMap implementation for Rust that provides **fine-grained locking at the key level**.

Unlike standard concurrent maps that might lock the entire map or large buckets, `LockMap` allows you to hold an exclusive lock on a specific key (including non-existent ones) for complex atomic operations, minimizing contention across different keys.

## Features

*   **Key-Level Locking**: Acquire exclusive locks for specific keys. Operations on different keys run in parallel.
*   **Sharding Architecture**: Internal sharding reduces contention on the map structure itself during insertions and removals.
*   **Deadlock Prevention**: Provides `batch_lock` to safely acquire locks on multiple keys simultaneously using a deterministic order.
*   **Efficient Waiting**: Uses a hybrid spin-then-park Futex implementation for low-overhead locking.
*   **Entry API**: Ergonomic RAII guards (`EntryByVal`, `EntryByRef`) for managing locks.

## Important Caveats

### 1. No Lock Poisoning

Unlike `std::sync::Mutex`, **this library does not implement lock poisoning**. If a thread panics while holding an `Entry`, the lock is released immediately (via Drop) to avoid deadlocks, but the data is **not** marked as poisoned.
> **Warning**: Users must ensure exception safety. If a panic occurs during a partial update, the data associated with that key may be left in an inconsistent state for subsequent readers.

### 2. `get()` Performance

The `map.get(key)` method clones the value while holding an internal shard lock.
> **Note**: If your value type `V` is expensive to clone (e.g., deep copy of large structures), or if `clone()` acquires other locks, use `map.entry(key).get()` instead. This moves the clone operation outside the internal map lock, preventing blocking of other threads accessing the same shard.

## Usage

```rust
use lockmap::LockMap;
use std::collections::BTreeSet;

// Create a new lock map
let map = LockMap::<String, String>::new();

// 1. Basic Insert
map.insert_by_ref("key", "value".into());

// 2. Get a value (Clones the value)
assert_eq!(map.get("key"), Some("value".into()));

// 3. Entry API: Exclusive access (Read/Write)
// This locks ONLY "key", other threads can access "other_key" concurrently.
{
    let mut entry = map.entry_by_ref("key");

    // Check value
    assert_eq!(entry.get().as_deref(), Some("value"));

    // Update value atomicity
    entry.insert("new value".to_string());
} // Lock is automatically released here

// 4. Remove a value
assert_eq!(map.remove("key"), Some("new value".into()));

// 5. Batch Locking (Deadlock safe)
// Acquires locks for multiple keys in a deterministic order.
let mut keys = BTreeSet::new();
keys.insert("key1".to_string());
keys.insert("key2".to_string());

// `locked_entries` holds all the locks
let mut locked_entries = map.batch_lock::<std::collections::HashMap<_, _>>(keys);

if let Some(mut entry) = locked_entries.get_mut("key1") {
   entry.insert("updated_in_batch".into());
}
// All locks released when `locked_entries` is dropped
```

## License

[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_large)
