//! A high-performance, thread-safe HashMap and LRU cache with fine-grained per-key locking.
//!
//! # Overview
//!
//! This crate provides two concurrent map implementations:
//!
//! - [`LockMap`]: A thread-safe HashMap with per-key level locking
//! - [`LruLockMap`]: A thread-safe LRU cache with per-key locking and automatic eviction
//!
//! Both data structures use internal sharding for high concurrency and allow you to
//! hold an exclusive lock on a specific key for complex atomic operations, minimizing
//! contention across different keys.
//!
//! # Features
//!
//! - **Per-key locking**: Acquire exclusive locks for specific keys; operations on different keys run in parallel
//! - **Sharding architecture**: Internal sharding reduces contention on the map structure itself
//! - **Single hash computation**: Key and pre-computed hash stored together; each operation hashes once
//! - **No key duplication**: Uses [`hashbrown::HashTable`] so each key is stored only once
//! - **Deadlock prevention**: `LockMap` provides [`batch_lock`](LockMap::batch_lock) for safe multi-key locking
//! - **Non-blocking locking**: [`try_entry`](LockMap::try_entry) returns `None` instead of blocking when a key is held
//! - **Iteration**: [`for_each`](LockMap::for_each) and [`retain`](LockMap::retain) visit all entries without a global lock
//! - **Pluggable hasher**: both maps accept a custom [`BuildHasher`](std::hash::BuildHasher) via `with_hasher` constructors
//! - **LRU eviction**: `LruLockMap` automatically evicts least recently used entries when capacity is exceeded
//! - **LRU inspection**: [`peek`](LruLockMap::peek) reads without promoting; [`pop_lru`](LruLockMap::pop_lru) removes a least-recently-used entry
//! - **Non-blocking eviction**: In-use entries are skipped during eviction; traversal continues to the next candidate
//!
//! # Examples
//!
//! ## LockMap
//!
//! ```
//! use lockmap::LockMap;
//!
//! let map = LockMap::<String, u32>::new();
//!
//! map.insert("key".to_string(), 42);
//! assert_eq!(map.get("key"), Some(42));
//!
//! {
//!     let mut entry = map.entry("key2".to_string());
//!     entry.insert(123);
//! }
//!
//! assert_eq!(map.remove("key"), Some(42));
//! ```
//!
//! ## LruLockMap
//!
//! ```
//! use lockmap::LruLockMap;
//!
//! let cache = LruLockMap::<String, u32>::new(1000);
//!
//! cache.insert("key".to_string(), 42);
//! assert_eq!(cache.get("key"), Some(42));
//!
//! {
//!     let mut entry = cache.entry("key2".to_string());
//!     entry.insert(123);
//! }
//!
//! assert_eq!(cache.remove("key"), Some(42));
//! ```

mod common;
mod lockmap;
mod lru_lockmap;

pub use lockmap::{Entry, LockMap};
pub use lru_lockmap::{LruEntry, LruLockMap};

/// Runs the code examples in `README.md` as documentation tests.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
pub struct ReadmeDoctests;
