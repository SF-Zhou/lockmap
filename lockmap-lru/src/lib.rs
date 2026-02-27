//! LRU-enabled variant of lockmap with automatic capacity management.
//!
//! This crate provides an LRU (Least Recently Used) cache built on top of `lockmap-core`.
//! It implements per-shard LRU eviction with an intrusive doubly-linked list design.
//!
//! # Features
//!
//! - **Per-shard LRU**: Each shard maintains its own LRU list, minimizing contention
//! - **Intrusive list design**: List nodes are embedded in State for cache-friendly access
//! - **Safe eviction**: Only evicts entries with refcnt == 0 (not currently in use)
//! - **Lazy cleanup**: Eviction happens on access to other keys, not immediately
//! - **Full API compatibility**: Supports the same entry API as standard lockmap
//!
//! # Examples
//!
//! ```
//! use lockmap_lru::LruLockMap;
//!
//! // Create an LRU map with capacity for 1000 entries per shard
//! let map = LruLockMap::<String, u32>::with_capacity_per_shard(1000);
//!
//! // Use like a normal LockMap
//! map.insert("key".into(), 42);
//! assert_eq!(map.get("key"), Some(42));
//!
//! // Oldest unused entries are automatically evicted when capacity is exceeded
//! ```

mod lru_list;
mod lru_lockmap;
#[cfg(test)]
mod lru_tests;

pub use lru_lockmap::*;
