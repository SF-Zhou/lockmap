# lockmap-lru

[![Crates.io](https://img.shields.io/crates/v/lockmap-lru.svg)](https://crates.io/crates/lockmap-lru)
[![Documentation](https://docs.rs/lockmap-lru/badge.svg)](https://docs.rs/lockmap-lru)

**lockmap-lru** is a high-performance, thread-safe LRU cache for Rust, built on top of the [lockmap](https://crates.io/crates/lockmap) architecture.

It provides **fine-grained per-key locking** combined with **automatic capacity-based eviction**. Each internal shard maintains its own LRU ordering via an intrusive doubly-linked list, ensuring that eviction decisions are local and lock-free from other shards.

## Features

*   **Per-Key Locking**: Acquire exclusive locks for specific keys. Operations on different keys run in parallel.
*   **Per-Shard LRU Eviction**: Each shard independently tracks access order and evicts the least recently used entries when capacity is exceeded.
*   **Non-Blocking Eviction**: In-use entries are skipped during eviction; traversal continues to the next candidate, ensuring eviction always makes progress.
*   **Intrusive Linked List**: LRU bookkeeping uses pointers embedded directly in each entry, avoiding extra allocations.
*   **No Key Duplication**: Uses `hashbrown::HashTable` so each key is stored only once (inside the entry state), saving memory and avoiding extra clones.
*   **Single Hash**: One `RandomState` hasher shared across all shards; each operation hashes the key once. Shard selection uses upper bits; the full hash is stored in each entry and reused for eviction and cleanup.
*   **Single-Probe Lookups**: Uses `HashTable::entry` / `HashTable::find_entry` for find-or-insert / find-or-remove in a single probe, avoiding double lookups.
*   **Entry API**: Ergonomic RAII guard (`LruEntry`) for managing locks. The key is obtained directly from the entry's internal state, eliminating redundant copies.

## Usage

```rust
use lockmap_lru::LruLockMap;

// Create a cache with capacity 1000
let cache = LruLockMap::<String, String>::new(1000);

// 1. Basic Insert
cache.insert_by_ref("key", "value".into());

// 2. Get a value (promotes it in the LRU list)
assert_eq!(cache.get("key"), Some("value".into()));

// 3. Entry API: Exclusive access
{
    let mut entry = cache.entry_by_ref("key");
    assert_eq!(entry.get().as_deref(), Some("value"));
    entry.insert("new_value".to_string());
} // Lock released here

// 4. Remove
assert_eq!(cache.remove("key"), Some("new_value".into()));
```

## LRU Eviction Details

- The total capacity is divided evenly among shards.
- On every access (get, insert, entry, remove, contains_key), the accessed entry is promoted to the head of its shard's LRU list.
- When a shard's entry count exceeds its capacity (after an insert or entry creation), the least recently used entries are evicted from the tail.
- Entries currently held by an `LruEntry` guard are **skipped** during eviction. Traversal continues from tail towards head, evicting any eligible entries, so eviction always makes progress even when the tail entry is held by another thread.

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or [MIT License](../LICENSE-MIT) at your option.
