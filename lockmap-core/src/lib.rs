//! Core components for lockmap: futex-based locking and sharded map structures.
//!
//! This crate provides the foundational building blocks used by both `lockmap`
//! and `lockmap-lru` implementations.
//!
//! # Components
//!
//! - **Futex-based Mutex**: A lightweight, high-performance mutex implementation
//!   using futex operations for efficient synchronization.
//! - **Sharded Map**: A concurrent map structure that uses sharding to reduce
//!   contention across multiple keys.

mod futex;
mod shards_map;

pub use futex::Mutex;
pub use shards_map::{ShardMap, ShardsMap, SimpleAction, UpdateAction};
