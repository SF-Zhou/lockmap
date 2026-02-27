# lockmap

[![Rust](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml/badge.svg)](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml)
[![codecov](https://codecov.io/gh/SF-Zhou/lockmap/graph/badge.svg?token=7U9JFC64U4)](https://codecov.io/gh/SF-Zhou/lockmap)
[![Crates.io](https://img.shields.io/crates/v/lockmap.svg)](https://crates.io/crates/lockmap)
[![Documentation](https://docs.rs/lockmap/badge.svg)](https://docs.rs/lockmap)
[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=shield)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_shield)

A family of high-performance, thread-safe concurrent map crates for Rust with **fine-grained per-key locking**.

## Workspace Crates

| Crate | Description |
|-------|-------------|
| [`lockmap-core`](lockmap-core/) | Shared infrastructure: fast futex-based mutex and sharded map primitives |
| [`lockmap`](lockmap/) | Thread-safe HashMap with per-key level locking |
| [`lockmap-lru`](lockmap-lru/) | Thread-safe LRU cache with per-key locking and automatic capacity-based eviction |

## lockmap

**LockMap** is a high-performance, thread-safe HashMap implementation that provides **fine-grained locking at the key level**.

Unlike standard concurrent maps that might lock the entire map or large buckets, `LockMap` allows you to hold an exclusive lock on a specific key (including non-existent ones) for complex atomic operations, minimizing contention across different keys.

### Features

*   **Key-Level Locking**: Acquire exclusive locks for specific keys. Operations on different keys run in parallel.
*   **Sharding Architecture**: Internal sharding reduces contention on the map structure itself during insertions and removals.
*   **Deadlock Prevention**: Provides `batch_lock` to safely acquire locks on multiple keys simultaneously using a deterministic order.
*   **Efficient Waiting**: Uses a hybrid spin-then-park Futex implementation for low-overhead locking.
*   **Entry API**: Ergonomic RAII guards (`EntryByVal`, `EntryByRef`) for managing locks.

### Usage

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

    // Update value atomically
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

## lockmap-lru

**LruLockMap** extends the per-key locking design with **LRU (Least Recently Used) eviction**. Each internal shard maintains its own LRU ordering via an intrusive doubly-linked list, ensuring that eviction decisions are local and lock-free from other shards.

### Features

*   **Per-Key Locking**: Same fine-grained locking as `lockmap`.
*   **Per-Shard LRU Eviction**: Each shard independently tracks access order and evicts least recently used entries when capacity is exceeded.
*   **Non-Blocking Eviction**: Entries currently held by an active guard are skipped during eviction — no blocking, no starvation.
*   **Intrusive Linked List**: LRU bookkeeping uses pointers embedded directly in each entry, avoiding extra allocations.

### Usage

```rust
use lockmap_lru::LruLockMap;

// Create a cache with capacity 1000
let cache = LruLockMap::<String, String>::new(1000);

// Insert and retrieve values
cache.insert_by_ref("key", "value".into());
assert_eq!(cache.get("key"), Some("value".into()));

// Entry API for exclusive access (promotes in LRU list)
{
    let mut entry = cache.entry_by_ref("key");
    entry.insert("new_value".to_string());
}

// Remove a value
assert_eq!(cache.remove("key"), Some("new_value".into()));

// When the cache exceeds capacity, the least recently used
// entries are automatically evicted.
```

## Important Caveats

### 1. No Lock Poisoning

Unlike `std::sync::Mutex`, **this library does not implement lock poisoning**. If a thread panics while holding an `Entry`, the lock is released immediately (via Drop) to avoid deadlocks, but the data is **not** marked as poisoned.
> **Warning**: Users must ensure exception safety. If a panic occurs during a partial update, the data associated with that key may be left in an inconsistent state for subsequent readers.

### 2. `get()` Performance

The `map.get(key)` method clones the value while holding an internal shard lock.
> **Note**: If your value type `V` is expensive to clone (e.g., deep copy of large structures), or if `clone()` acquires other locks, use `map.entry(key).get()` instead. This moves the clone operation outside the internal map lock, preventing blocking of other threads accessing the same shard.

## License

[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_large)
