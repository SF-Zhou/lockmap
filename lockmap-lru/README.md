# lockmap-lru

[![Crates.io](https://img.shields.io/crates/v/lockmap-lru.svg)](https://crates.io/crates/lockmap-lru)
[![Documentation](https://docs.rs/lockmap-lru/badge.svg)](https://docs.rs/lockmap-lru)

**LockMap-LRU** is an LRU (Least Recently Used) cache built on top of lockmap-core, providing automatic capacity management with per-shard LRU eviction.

## Features

- **Per-Shard LRU**: Each shard maintains its own LRU list, minimizing contention
- **Intrusive List Design**: List nodes are embedded directly in State for cache-friendly access
- **Automatic Eviction**: Automatically evicts least recently used entries when capacity is exceeded
- **Thread-Safe**: Fully thread-safe with per-shard locking
- **Simple API**: Compatible API with standard map operations

## Usage

```rust
use lockmap_lru::LruLockMap;

// Create an LRU map with capacity for 1000 entries per shard
let map = LruLockMap::<String, u32>::with_capacity_per_shard(1000);

// Use it like a regular map
map.insert("key1".into(), 42);
map.insert("key2".into(), 100);

// Access updates LRU position
assert_eq!(map.get("key1"), Some(42));

// When capacity is exceeded, least recently used entries are evicted
for i in 0..2000 {
    map.insert(format!("key{}", i), i);
}

// Older entries may have been evicted
assert!(map.get("key1").is_none());
```

## How It Works

1. **Per-Shard Architecture**: The map is divided into multiple shards, each with its own capacity limit and LRU list
2. **Access Tracking**: Every `get`, `insert`, or `contains_key` operation moves the accessed entry to the head of the LRU list
3. **Automatic Eviction**: When inserting a new entry would exceed the shard's capacity, entries are evicted from the tail of the LRU list
4. **Intrusive List**: The LRU list uses an intrusive doubly-linked list design, where list nodes are embedded directly in the state structure for better cache locality

## Performance Characteristics

- **O(1)** for get, insert, remove operations (amortized)
- **O(1)** LRU list updates on access
- **Per-shard locking** for high concurrency
- **Memory efficient** through intrusive list design

## Differences from Standard LockMap

- Requires `K: Clone` for all operations due to eviction needs
- Does not support the full `entry()` API (simplified implementation)
- Automatically evicts entries when capacity is exceeded
- Slightly higher memory overhead for LRU tracking

## License

Licensed under either of Apache License, Version 2.0 or MIT license at your option.
