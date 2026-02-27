//! A high-performance, thread-safe LRU cache with per-key locking.
//!
//! # Overview
//!
//! `lockmap-lru` provides a concurrent LRU (Least Recently Used) cache built on
//! the [`lockmap`](https://crates.io/crates/lockmap) architecture. It combines
//! fine-grained per-key locking with automatic capacity-based eviction.
//!
//! Each shard maintains its own LRU list using an intrusive doubly-linked list
//! embedded in the entry state. On every access, the accessed entry is promoted
//! to the head of the list. When a shard exceeds its capacity, the least recently
//! used entries are evicted from the tail. In-use entries (held by an [`LruEntry`]
//! guard) are skipped and eviction continues to the next candidate, ensuring
//! progress even when the tail entry is held by another thread.
//!
//! # Features
//!
//! - **Per-key locking**: Same fine-grained locking as `lockmap`
//! - **Per-shard LRU eviction**: Each shard independently manages its own LRU list
//! - **Non-blocking eviction**: Entries currently in use are skipped; eviction walks past them to evict other candidates
//! - **Intrusive linked list**: Zero-allocation LRU bookkeeping via pointers embedded in each entry
//!
//! # Examples
//!
//! ```
//! use lockmap_lru::LruLockMap;
//!
//! // Create an LRU cache with capacity 100
//! let cache = LruLockMap::<String, u32>::new(100);
//!
//! // Basic operations
//! cache.insert("key1".to_string(), 42);
//! assert_eq!(cache.get("key1"), Some(42));
//!
//! // Entry API for exclusive access
//! {
//!     let mut entry = cache.entry("key2".to_string());
//!     entry.insert(123);
//! }
//!
//! // Remove a value
//! assert_eq!(cache.remove("key1"), Some(42));
//! assert_eq!(cache.get("key1"), None);
//! ```
#[doc = include_str!("../README.md")]
mod lru_lockmap;

pub use lru_lockmap::*;
