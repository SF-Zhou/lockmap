//! Request coalescing ("singleflight"): when many threads miss the same cache
//! key simultaneously, only one of them performs the expensive load; the
//! others block on that key's lock — and only that key — then reuse the
//! freshly inserted value.
//!
//! This is the signature use case for per-key locking: a shard-level lock
//! (e.g. `dashmap`) would also stall unrelated keys that happen to live in the
//! same shard, while a global lock would stall the entire cache.
//!
//! Run with: `cargo run --example singleflight`

use lockmap::LockMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::Duration;

static BACKEND_LOADS: AtomicUsize = AtomicUsize::new(0);

/// Simulates a slow backend (database, RPC, disk...).
fn load_from_backend(key: &str) -> String {
    BACKEND_LOADS.fetch_add(1, Ordering::Relaxed);
    thread::sleep(Duration::from_millis(100));
    format!("value-of-{key}")
}

/// Cache-aside read with request coalescing.
fn get_or_load(cache: &LockMap<String, String>, key: &str) -> String {
    // Fast path: no per-key lock is taken if the value is already cached.
    if let Some(value) = cache.get(key) {
        return value;
    }

    // Slow path: lock this key exclusively. Exactly one thread runs the
    // closure; the others wait on the same key and then find the value
    // already present, so the backend is hit only once.
    let mut entry = cache.entry_by_ref(key);
    entry.or_insert_with(|| load_from_backend(key)).clone()
}

fn main() {
    let cache = LockMap::<String, String>::new();

    thread::scope(|s| {
        for i in 0..8 {
            let cache = &cache;
            s.spawn(move || {
                let value = get_or_load(cache, "hot-key");
                println!("thread {i}: got {value:?}");
            });
        }
    });

    let loads = BACKEND_LOADS.load(Ordering::Relaxed);
    println!("backend loads for 8 concurrent requests: {loads}");
    assert_eq!(loads, 1, "the backend must be hit exactly once");
}
