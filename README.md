# lockmap

[![Rust](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml/badge.svg)](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml)
[![codecov](https://codecov.io/gh/SF-Zhou/lockmap/graph/badge.svg?token=7U9JFC64U4)](https://codecov.io/gh/SF-Zhou/lockmap)
[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=shield)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_shield)

**LockMap** is a collection of high-performance, thread-safe HashMap implementations for Rust that provide fine-grained locking and specialized features.

This repository contains a workspace with three crates:

## Crates

### lockmap-core

Core components shared across all lockmap implementations:
- Futex-based mutex for efficient synchronization
- Sharded map structure for high concurrency
- Common traits and utilities

### lockmap

[![Crates.io](https://img.shields.io/crates/v/lockmap.svg)](https://crates.io/crates/lockmap)
[![Documentation](https://docs.rs/lockmap/badge.svg)](https://docs.rs/lockmap)

The main **LockMap** implementation with key-level locking:

- **Key-Level Locking**: Acquire exclusive locks for specific keys
- **Sharding Architecture**: Internal sharding reduces contention
- **Deadlock Prevention**: `batch_lock` for safely acquiring multiple locks
- **Efficient Waiting**: Hybrid spin-then-park Futex implementation
- **Entry API**: Ergonomic RAII guards for managing locks

```rust
use lockmap::LockMap;

let map = LockMap::<String, u32>::new();
map.insert("key".into(), 42);

// Entry API for exclusive access
{
    let mut entry = map.entry("key".into());
    entry.insert(100);
}
```

See [lockmap/README.md](lockmap/README.md) for full documentation.

### lockmap-lru

[![Crates.io](https://img.shields.io/crates/v/lockmap-lru.svg)](https://crates.io/crates/lockmap-lru)
[![Documentation](https://docs.rs/lockmap-lru/badge.svg)](https://docs.rs/lockmap-lru)

An LRU (Least Recently Used) cache with automatic capacity management:

- **Per-Shard LRU**: Each shard maintains its own LRU list
- **Intrusive List Design**: Embedded list nodes for cache efficiency
- **Automatic Eviction**: Evicts least recently used entries when capacity is exceeded
- **Thread-Safe**: Per-shard locking for high concurrency

```rust
use lockmap_lru::LruLockMap;

// Create with capacity for 1000 entries per shard
let map = LruLockMap::<String, u32>::with_capacity_per_shard(1000);

map.insert("key".into(), 42);
assert_eq!(map.get("key"), Some(42));

// Oldest entries are automatically evicted when capacity is exceeded
```

See [lockmap-lru/README.md](lockmap-lru/README.md) for full documentation.

## Architecture

The workspace is organized as follows:

```
lockmap/
├── lockmap-core/     # Core components (futex, sharding)
├── lockmap/          # Main lockmap implementation
└── lockmap-lru/      # LRU variant with automatic eviction
```

All crates share the same core infrastructure but provide different APIs and guarantees optimized for specific use cases.

## Important Caveats

### 1. No Lock Poisoning

Unlike `std::sync::Mutex`, these libraries do not implement lock poisoning. If a thread panics while holding a lock, the lock is released immediately (via Drop) to avoid deadlocks, but the data is **not** marked as poisoned.

> **Warning**: Users must ensure exception safety. If a panic occurs during a partial update, the data may be left in an inconsistent state.

### 2. `get()` Performance

The `map.get(key)` method clones the value while holding an internal shard lock. If your value type is expensive to clone, consider using the entry API (`lockmap`) or ensure your value type has an efficient `Clone` implementation.

## Performance

All implementations use:
- **Sharded architecture** for reduced contention
- **Futex-based locking** for efficient synchronization
- **Per-shard hash maps** for O(1) average-case operations
- **Lock-free fast paths** where possible

## License

[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_large)

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.
