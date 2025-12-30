//! A thread-safe hashmap implementation providing per-key level locking and atomic operations.
//!
//! # Overview
//! `lockmap` provides a concurrent hashmap implementation that allows fine-grained locking at the key level.
//! It uses internal sharding for better performance under high concurrency.
//!
//! # Features
//! - Thread-safe access with per-key locking
//! - Entry API for exclusive access to values
//! - Efficient concurrent operations through sharding
//! - Safe atomic updates
//! - No poisoning, the lock is released normally on panic
//!
//! # Examples
//! ```
//! use lockmap::LockMap;
//!
//! let map = LockMap::<String, u32>::new();
//!
//! // Basic operations
//! map.insert("key1".into(), 42);
//! assert_eq!(map.get("key1"), Some(42));
//!
//! // Entry API for exclusive access
//! {
//!     let mut entry = map.entry("key2".into());
//!     entry.get_mut().replace(123);
//! }
//!
//! // Remove a value
//! assert_eq!(map.remove("key1"), Some(42));
//! assert_eq!(map.get("key1"), None);
//! ```
mod futex;
#[doc = include_str!("../README.md")]
mod lockmap;
mod shards_map;

use futex::*;
pub use lockmap::*;
use shards_map::*;
