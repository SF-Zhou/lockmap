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
//!
//! # Examples
//! ```
//! use lockmap::LockMap;
//!
//! let map = LockMap::<String, u32>::new();
//!
//! // Basic operations
//! map.set("key1".into(), 42);
//! assert_eq!(map.get("key1".into()), Some(42));
//!
//! // Entry API for exclusive access
//! {
//!     let entry = map.entry("key2".into());
//!     entry.value.replace(123);
//! }
//! ```
#[doc = include_str!("../README.md")]
mod lockmap;
mod shards_map;
mod waiter;

pub use lockmap::*;
use shards_map::*;
use waiter::*;
