//! Per-key token-bucket rate limiter.
//!
//! Each user owns an independent bucket protected by its own lock, so the
//! refill-and-consume critical section of one user never contends with
//! another user's requests.
//!
//! Run with: `cargo run --example rate_limiter`

use lockmap::LockMap;
use std::time::{Duration, Instant};

struct Bucket {
    tokens: f64,
    last_refill: Instant,
}

struct RateLimiter {
    buckets: LockMap<String, Bucket>,
    capacity: f64,
    refill_per_sec: f64,
}

impl RateLimiter {
    fn new(capacity: f64, refill_per_sec: f64) -> Self {
        Self {
            buckets: LockMap::new(),
            capacity,
            refill_per_sec,
        }
    }

    /// Tries to take one token from `user`'s bucket.
    ///
    /// The whole read-modify-write below is atomic for this user because the
    /// entry guard holds the per-key lock, yet requests from other users
    /// proceed in parallel.
    fn try_acquire(&self, user: &str) -> bool {
        let mut entry = self.buckets.entry_by_ref(user);
        let now = Instant::now();
        let bucket = entry.or_insert_with(|| Bucket {
            tokens: self.capacity,
            last_refill: now,
        });

        let elapsed = now.duration_since(bucket.last_refill).as_secs_f64();
        bucket.tokens = (bucket.tokens + elapsed * self.refill_per_sec).min(self.capacity);
        bucket.last_refill = now;

        if bucket.tokens >= 1.0 {
            bucket.tokens -= 1.0;
            true
        } else {
            false
        }
    }
}

fn main() {
    // 5 tokens burst capacity, refills at 10 tokens per second.
    let limiter = RateLimiter::new(5.0, 10.0);

    // A burst of 8 requests from alice: 5 pass, 3 are rejected.
    let (mut allowed, mut rejected) = (0, 0);
    for _ in 0..8 {
        if limiter.try_acquire("alice") {
            allowed += 1;
        } else {
            rejected += 1;
        }
    }
    println!("alice burst: {allowed} allowed, {rejected} rejected");
    assert_eq!((allowed, rejected), (5, 3));

    // bob has his own bucket and is unaffected by alice's burst.
    assert!(limiter.try_acquire("bob"));
    println!("bob: allowed");

    // After 300ms alice's bucket has refilled ~3 tokens.
    std::thread::sleep(Duration::from_millis(300));
    assert!(limiter.try_acquire("alice"));
    println!("alice after refill: allowed");
}
