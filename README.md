# lockmap

[![Rust](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml/badge.svg)](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml)
[![codecov](https://codecov.io/gh/SF-Zhou/lockmap/graph/badge.svg?token=7U9JFC64U4)](https://codecov.io/gh/SF-Zhou/lockmap)
[![Crates.io](https://img.shields.io/crates/v/lockmap.svg)](https://crates.io/crates/lockmap)
[![Crates.io Downloads](https://img.shields.io/crates/d/lockmap.svg)](https://crates.io/crates/lockmap)
[![Documentation](https://docs.rs/lockmap/badge.svg)](https://docs.rs/lockmap)
[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=shield)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_shield)

A high-performance, thread-safe HashMap and LRU cache for Rust with **fine-grained per-key locking**.

## Data Structures

| Type | Description |
|------|-------------|
| [`LockMap`](https://docs.rs/lockmap/latest/lockmap/struct.LockMap.html) | Thread-safe HashMap with per-key level locking |
| [`LruLockMap`](https://docs.rs/lockmap/latest/lockmap/struct.LruLockMap.html) | Thread-safe LRU cache with per-key locking and automatic capacity-based eviction |

## LockMap

**LockMap** is a high-performance, thread-safe HashMap implementation that provides **fine-grained locking at the key level**.

Unlike standard concurrent maps that might lock the entire map or large buckets, `LockMap` allows you to hold an exclusive lock on a specific key (including non-existent ones) for complex atomic operations, minimizing contention across different keys.

### Features

*   **Key-Level Locking**: Acquire exclusive locks for specific keys. Operations on different keys run in parallel.
*   **Sharding Architecture**: Internal sharding reduces contention on the map structure itself during insertions and removals.
*   **Deadlock Prevention**: Provides `batch_lock` to safely acquire locks on multiple keys simultaneously using a deterministic order.
*   **Non-Blocking Locking**: `try_entry` / `try_entry_by_ref` return `None` instead of blocking when a key is already held.
*   **Single Hash Computation**: Each key is hashed once; the pre-computed hash is stored alongside the key and reused for shard selection, table probing, and rehashing.
*   **No Key Duplication**: Uses `hashbrown::HashTable` so each key is stored only once, inside the entry state.
*   **Entry API**: Ergonomic unified RAII guard (`Entry`) for managing locks.

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

// 4. Non-blocking access: returns None if the key is currently held
if let Some(mut entry) = map.try_entry_by_ref("key") {
    entry.insert("another value".to_string());
}

// 5. Remove a value
assert_eq!(map.remove("key"), Some("another value".into()));

// 6. Batch Locking (Deadlock safe)
// Acquires locks for multiple keys in a deterministic order.
let mut keys = BTreeSet::new();
keys.insert("key1".to_string());
keys.insert("key2".to_string());

// `locked_entries` holds all the locks
let mut locked_entries = map.batch_lock::<std::collections::HashMap<_, _>>(keys);

if let Some(entry) = locked_entries.get_mut("key1") {
   entry.insert("updated_in_batch".into());
}
// All locks released when `locked_entries` is dropped
drop(locked_entries);

// 7. Clear the map (waits for held entries, like `remove`)
map.clear();
assert!(map.is_empty());
```

## LruLockMap

**LruLockMap** extends the per-key locking design with **LRU (Least Recently Used) eviction**. Each internal shard maintains its own LRU ordering via an intrusive doubly-linked list, ensuring that eviction decisions are local and lock-free from other shards.

### Features

*   **Per-Key Locking**: Same fine-grained locking as `LockMap`.
*   **Per-Shard LRU Eviction**: Each shard independently tracks access order and evicts least recently used entries when capacity is exceeded.
*   **`peek` / `pop_lru`**: Read a value without promoting it in the LRU list, or explicitly remove a least-recently-used entry.
*   **Non-Blocking Eviction**: In-use entries are skipped during eviction; traversal continues to the next candidate, ensuring progress even when the tail is held.
*   **Intrusive Linked List**: LRU bookkeeping uses pointers embedded directly in each entry, avoiding extra allocations.
*   **No Key Duplication**: Uses `hashbrown::HashTable` so each key is stored only once, inside the entry state.
*   **Single Hash, Single Probe**: One hasher for the whole map; each operation hashes once. Uses `HashTable::entry` / `find_entry` for single-probe find-or-insert/remove.

### Usage

```rust
use lockmap::LruLockMap;

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

// Peek without promoting the entry in the LRU list
assert_eq!(cache.peek("key"), Some("new_value".into()));

// Explicitly pop a least-recently-used entry
assert_eq!(cache.pop_lru(), Some(("key".to_string(), "new_value".to_string())));

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

## Changelog

See [CHANGELOG.md](CHANGELOG.md) for release notes and migration guides.

## License

[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_large)
