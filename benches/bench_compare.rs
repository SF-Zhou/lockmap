//! Comparison benchmarks against `dashmap` and `moka`.
//!
//! # Fairness notes
//!
//! The three crates have different semantics, so the workloads are normalized
//! to the closest common behaviour:
//!
//! - **get**: `LockMap::get` and `moka::sync::Cache::get` return a clone of the
//!   value; `DashMap::get` returns a guard, so the value is copied out of the
//!   guard (`V = u64`, clone == copy).
//! - **entry**: `LockMap::entry` locks a single key; `DashMap::entry` locks the
//!   whole shard. `moka` has no comparable exclusive-entry API and is excluded
//!   from that group.
//! - **LRU eviction**: `LruLockMap` evicts synchronously per shard; `moka`
//!   batches eviction internally. `DashMap` has no eviction and is excluded
//!   from that group.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use dashmap::DashMap;
use lockmap::{LockMap, LruLockMap};
use moka::sync::Cache as MokaCache;
use std::hint::black_box;
use std::thread;
use std::time::Duration;

/// Thread counts used for the concurrent benchmarks.
const THREAD_COUNTS: &[usize] = &[1, 4, 8];

/// Operations performed by each thread per benchmark iteration.
const OPS_PER_THREAD: usize = 1 << 14;

/// Simple xorshift64 PRNG: deterministic and cheap, so the RNG does not
/// dominate the measured map operations.
#[inline]
fn xorshift(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

#[inline]
fn seed(thread: usize) -> u64 {
    (thread as u64 + 1) * 0x9E37_79B9_7F4A_7C15
}

fn configure(group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>) {
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(1));
    group.measurement_time(Duration::from_secs(3));
}

/// Runs `op` on `threads` scoped threads, `OPS_PER_THREAD` times each, feeding
/// it a per-thread RNG.
fn run_threads<F>(threads: usize, op: F)
where
    F: Fn(&mut u64) + Sync,
{
    thread::scope(|s| {
        for t in 0..threads {
            let op = &op;
            s.spawn(move || {
                let mut rng = seed(t);
                for _ in 0..OPS_PER_THREAD {
                    op(&mut rng);
                }
            });
        }
    });
}

// ---------------------------------------------------------------------------
// Concurrent get (all hits)
// ---------------------------------------------------------------------------

fn bench_compare_get(c: &mut Criterion) {
    const KEYS: u64 = 1 << 16;

    let lockmap = LockMap::<u64, u64>::with_capacity(KEYS as usize);
    let dashmap = DashMap::<u64, u64>::with_capacity(KEYS as usize);
    let moka = MokaCache::<u64, u64>::new(KEYS * 2);
    for i in 0..KEYS {
        lockmap.insert(i, i);
        dashmap.insert(i, i);
        moka.insert(i, i);
    }

    let mut group = c.benchmark_group("compare_get");
    configure(&mut group);
    for &threads in THREAD_COUNTS {
        group.throughput(Throughput::Elements((threads * OPS_PER_THREAD) as u64));
        group.bench_with_input(BenchmarkId::new("lockmap", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let key = xorshift(rng) % KEYS;
                    black_box(lockmap.get(&key));
                })
            })
        });
        group.bench_with_input(BenchmarkId::new("dashmap", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let key = xorshift(rng) % KEYS;
                    black_box(dashmap.get(&key).map(|v| *v));
                })
            })
        });
        group.bench_with_input(BenchmarkId::new("moka", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let key = xorshift(rng) % KEYS;
                    black_box(moka.get(&key));
                })
            })
        });
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Concurrent mixed: 90% get / 10% insert
// ---------------------------------------------------------------------------

fn bench_compare_mixed(c: &mut Criterion) {
    const KEYS: u64 = 1 << 16;

    let lockmap = LockMap::<u64, u64>::with_capacity(KEYS as usize);
    let dashmap = DashMap::<u64, u64>::with_capacity(KEYS as usize);
    let moka = MokaCache::<u64, u64>::new(KEYS * 2);
    for i in 0..KEYS {
        lockmap.insert(i, i);
        dashmap.insert(i, i);
        moka.insert(i, i);
    }

    let mut group = c.benchmark_group("compare_mixed");
    configure(&mut group);
    for &threads in THREAD_COUNTS {
        group.throughput(Throughput::Elements((threads * OPS_PER_THREAD) as u64));
        group.bench_with_input(BenchmarkId::new("lockmap", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let r = xorshift(rng);
                    let key = r % KEYS;
                    if r % 10 == 0 {
                        lockmap.insert(key, key);
                    } else {
                        black_box(lockmap.get(&key));
                    }
                })
            })
        });
        group.bench_with_input(BenchmarkId::new("dashmap", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let r = xorshift(rng);
                    let key = r % KEYS;
                    if r % 10 == 0 {
                        dashmap.insert(key, key);
                    } else {
                        black_box(dashmap.get(&key).map(|v| *v));
                    }
                })
            })
        });
        group.bench_with_input(BenchmarkId::new("moka", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let r = xorshift(rng);
                    let key = r % KEYS;
                    if r % 10 == 0 {
                        moka.insert(key, key);
                    } else {
                        black_box(moka.get(&key));
                    }
                })
            })
        });
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Hot-key entry contention (exclusive per-key access)
// ---------------------------------------------------------------------------

fn bench_compare_hot_key_entry(c: &mut Criterion) {
    const HOT_KEYS: u64 = 8;

    let lockmap = LockMap::<u64, u64>::new();
    let dashmap = DashMap::<u64, u64>::new();
    for i in 0..HOT_KEYS {
        lockmap.insert(i, 0);
        dashmap.insert(i, 0);
    }

    let mut group = c.benchmark_group("compare_hot_key_entry");
    configure(&mut group);
    for &threads in THREAD_COUNTS {
        group.throughput(Throughput::Elements((threads * OPS_PER_THREAD) as u64));
        group.bench_with_input(BenchmarkId::new("lockmap", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let key = xorshift(rng) % HOT_KEYS;
                    let mut entry = lockmap.entry(key);
                    if let Some(v) = entry.get_mut() {
                        *v = v.wrapping_add(1);
                    }
                })
            })
        });
        group.bench_with_input(BenchmarkId::new("dashmap", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let key = xorshift(rng) % HOT_KEYS;
                    let mut entry = dashmap.entry(key).or_insert(0);
                    *entry = entry.wrapping_add(1);
                })
            })
        });
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// LRU: mixed workload under eviction pressure
// ---------------------------------------------------------------------------

fn bench_compare_lru_evict(c: &mut Criterion) {
    const KEYS: u64 = 1 << 16;
    const CAPACITY: u64 = 1 << 14;

    let lru = LruLockMap::<u64, u64>::new(CAPACITY as usize);
    let moka = MokaCache::<u64, u64>::new(CAPACITY);

    let mut group = c.benchmark_group("compare_lru_evict");
    configure(&mut group);
    for &threads in THREAD_COUNTS {
        group.throughput(Throughput::Elements((threads * OPS_PER_THREAD) as u64));
        group.bench_with_input(BenchmarkId::new("lockmap", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let r = xorshift(rng);
                    let key = r % KEYS;
                    if r % 2 == 0 {
                        lru.insert(key, key);
                    } else {
                        black_box(lru.get(&key));
                    }
                })
            })
        });
        group.bench_with_input(BenchmarkId::new("moka", threads), &threads, |b, &t| {
            b.iter(|| {
                run_threads(t, |rng| {
                    let r = xorshift(rng);
                    let key = r % KEYS;
                    if r % 2 == 0 {
                        moka.insert(key, key);
                    } else {
                        black_box(moka.get(&key));
                    }
                })
            })
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_compare_get,
    bench_compare_mixed,
    bench_compare_hot_key_entry,
    bench_compare_lru_evict,
);
criterion_main!(benches);
