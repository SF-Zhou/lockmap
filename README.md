# lockmap

[![Rust](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml/badge.svg)](https://github.com/SF-Zhou/lockmap/actions/workflows/rust.yml)
[![codecov](https://codecov.io/gh/SF-Zhou/lockmap/graph/badge.svg?token=7U9JFC64U4)](https://codecov.io/gh/SF-Zhou/lockmap)
[![Crates.io](https://img.shields.io/crates/v/lockmap.svg)](https://crates.io/crates/lockmap)
[![Crates.io Downloads](https://img.shields.io/crates/d/lockmap.svg)](https://crates.io/crates/lockmap)
[![Documentation](https://docs.rs/lockmap/badge.svg)](https://docs.rs/lockmap)
[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=shield)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_shield)

A high-performance, thread-safe HashMap and LRU cache for Rust with **fine-grained per-key locking**.

Correctness is taken seriously: every commit is verified in CI with **Miri** and **ThreadSanitizer** over the full concurrent test suite, plus an MSRV check, `clippy -D warnings`, and tests across five OS/architecture targets.

## Installation

```bash
cargo add lockmap
```

Or add it to your `Cargo.toml` manually:

```toml
[dependencies]
lockmap = "0.2"
```

The minimum supported Rust version (MSRV) is **1.75**, verified in CI.

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
*   **Iteration**: `for_each` / `retain` visit all entries shard by shard, without a global lock.
*   **Pluggable Hasher**: Both maps accept a custom `BuildHasher` via `with_hasher` constructors (default: `foldhash`).
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
*   **Batch Locking**: Same deadlock-safe `batch_lock` as `LockMap`; keys held by guards are never evicted.
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

## Examples

Runnable, self-checking examples live in [`examples/`](examples/):

| Example | What it shows |
|---------|---------------|
| [`singleflight.rs`](examples/singleflight.rs) | Request coalescing: 8 threads miss the same key, the backend is hit exactly once |
| [`rate_limiter.rs`](examples/rate_limiter.rs) | Per-user token-bucket rate limiter with atomic refill-and-consume per key |
| [`lru_session_store.rs`](examples/lru_session_store.rs) | Bounded session store using LRU eviction, `peek` and `pop_lru` |

```bash
cargo run --example singleflight
```

## Comparison with Alternatives

Capability matrix (see the [Benchmarks](#benchmarks) section for performance trade-offs):

| Capability | `lockmap` | `dashmap` | `moka` |
|------------|-----------|-----------|--------|
| Exclusive lock granularity | per key | per shard | no lock API |
| Holding a guard blocks | that key only | the whole shard | — |
| Locking a not-yet-existing key | ✅ | ✅ (holds the shard) | ❌ |
| Deadlock-safe multi-key locking | ✅ `batch_lock` | ❌ | ❌ |
| Bounded capacity with eviction | ✅ per-shard LRU | ❌ | ✅ TinyLFU |
| Non-promoting read / explicit pop | ✅ `peek` / `pop_lru` | — | ❌ |

Rule of thumb: pick `lockmap` when you need **exclusive per-key critical sections** (read-modify-write, request coalescing, per-key state machines) or a **throughput-oriented bounded cache**; pick `dashmap` for a general concurrent map with short operations; pick `moka` when **cache hit rate** is the primary concern.

## Benchmarks

The repository ships two Criterion benchmark suites:

```bash
cargo bench --bench bench_lockmap   # multi-threaded workloads for LockMap / LruLockMap
cargo bench --bench bench_compare   # comparison against dashmap and moka
```

The comparison suite normalizes semantics where the crates differ (see the
fairness notes in `benches/bench_compare.rs`). Rough expectations: `LockMap`
trades a little single-thread overhead for per-key exclusive access — under
short critical sections `DashMap`'s shard lock is faster on hot keys, while
`LockMap` scales better on mixed/read workloads and never blocks unrelated keys
while an entry is held. `moka` maintains hit-rate-oriented bookkeeping (TinyLFU)
and targets a different trade-off than `LruLockMap`'s raw-throughput sharded LRU;
run the suite on your own hardware and workload before drawing conclusions.

## Important Caveats

### 1. Locks Are Not Reentrant

Calling any map operation for a key **while already holding that key's `Entry`** deadlocks — this includes `get`, `insert`, `remove`, `entry`, and whole-map operations such as `clear`, `for_each` and `retain`.
> **Note**: Drop the guard first, or use `try_entry` / `try_entry_by_ref` when you cannot statically rule out re-entry.

### 2. No Lock Poisoning

Unlike `std::sync::Mutex`, **this library does not implement lock poisoning**. If a thread panics while holding an `Entry`, the lock is released immediately (via Drop) to avoid deadlocks, but the data is **not** marked as poisoned.
> **Warning**: Users must ensure exception safety. If a panic occurs during a partial update, the data associated with that key may be left in an inconsistent state for subsequent readers.

### 3. `get()` Performance

The `map.get(key)` method clones the value while holding an internal shard lock.
> **Note**: If your value type `V` is expensive to clone (e.g., deep copy of large structures), or if `clone()` acquires other locks, use `map.entry(key).get()` instead. This moves the clone operation outside the internal map lock, preventing blocking of other threads accessing the same shard.

## Changelog

See [CHANGELOG.md](CHANGELOG.md) for release notes and migration guides.

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.

[![FOSSA Status](https://app.fossa.com/api/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap.svg?type=large)](https://app.fossa.com/projects/git%2Bgithub.com%2FSF-Zhou%2Flockmap?ref=badge_large)
