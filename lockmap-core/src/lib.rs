//! Core utilities for the lockmap family of crates.
//!
//! This crate provides:
//! - A fast, futex-based [`Mutex`] for low-overhead synchronization
//! - [`ShardsMap`] and [`ShardMap`] for sharded concurrent map infrastructure
//! - [`SimpleAction`] and [`UpdateAction`] enums for map update operations

mod futex;
mod shards_map;

pub use futex::*;
pub use shards_map::*;
