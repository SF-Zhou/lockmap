use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use lockmap::{LockMap, LruLockMap};
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

// ---------------------------------------------------------------------------
// LockMap
// ---------------------------------------------------------------------------

/// Single-threaded bulk insert into a fresh map (allocation + growth path).
fn bench_lockmap_insert(c: &mut Criterion) {
    let count = 1 << 20;
    let mut group = c.benchmark_group("lockmap_insert");
    configure(&mut group);
    group.throughput(Throughput::Elements(count as u64));
    group.bench_with_input(BenchmarkId::from_parameter(count), &count, |b, &count| {
        b.iter(|| {
            let map = LockMap::with_capacity_and_shard_amount(1 << 15, 256);
            for i in 0..count {
                map.insert(i, i);
            }
            black_box(map)
        })
    });
    group.finish();
}

/// Concurrent read-only workload over a prefilled map (all hits).
fn bench_lockmap_concurrent_get(c: &mut Criterion) {
    const KEYS: u64 = 1 << 16;
    let map = LockMap::<u64, u64>::with_capacity(KEYS as usize);
    for i in 0..KEYS {
        map.insert(i, i);
    }

    let mut group = c.benchmark_group("lockmap_concurrent_get");
    configure(&mut group);
    for &threads in THREAD_COUNTS {
        group.throughput(Throughput::Elements((threads * OPS_PER_THREAD) as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(threads),
            &threads,
            |b, &threads| {
                b.iter(|| {
                    thread::scope(|s| {
                        for t in 0..threads {
                            let map = &map;
                            s.spawn(move || {
                                let mut rng = seed(t);
                                let mut sum = 0u64;
                                for _ in 0..OPS_PER_THREAD {
                                    let key = xorshift(&mut rng) % KEYS;
                                    if let Some(v) = map.get(&key) {
                                        sum = sum.wrapping_add(v);
                                    }
                                }
                                black_box(sum);
                            });
                        }
                    });
                })
            },
        );
    }
    group.finish();
}

/// Concurrent mixed workload: 90% get / 10% insert over random keys.
fn bench_lockmap_concurrent_mixed(c: &mut Criterion) {
    const KEYS: u64 = 1 << 16;
    let map = LockMap::<u64, u64>::with_capacity(KEYS as usize);
    for i in 0..KEYS {
        map.insert(i, i);
    }

    let mut group = c.benchmark_group("lockmap_concurrent_mixed");
    configure(&mut group);
    for &threads in THREAD_COUNTS {
        group.throughput(Throughput::Elements((threads * OPS_PER_THREAD) as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(threads),
            &threads,
            |b, &threads| {
                b.iter(|| {
                    thread::scope(|s| {
                        for t in 0..threads {
                            let map = &map;
                            s.spawn(move || {
                                let mut rng = seed(t);
                                for _ in 0..OPS_PER_THREAD {
                                    let r = xorshift(&mut rng);
                                    let key = r % KEYS;
                                    if r % 10 == 0 {
                                        map.insert(key, key);
                                    } else {
                                        black_box(map.get(&key));
                                    }
                                }
                            });
                        }
                    });
                })
            },
        );
    }
    group.finish();
}

/// Heavy contention on a small set of hot keys via the entry API.
fn bench_lockmap_hot_key_entry(c: &mut Criterion) {
    const HOT_KEYS: u64 = 8;
    let map = LockMap::<u64, u64>::new();
    for i in 0..HOT_KEYS {
        map.insert(i, 0);
    }

    let mut group = c.benchmark_group("lockmap_hot_key_entry");
    configure(&mut group);
    for &threads in THREAD_COUNTS {
        group.throughput(Throughput::Elements((threads * OPS_PER_THREAD) as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(threads),
            &threads,
            |b, &threads| {
                b.iter(|| {
                    thread::scope(|s| {
                        for t in 0..threads {
                            let map = &map;
                            s.spawn(move || {
                                let mut rng = seed(t);
                                for _ in 0..OPS_PER_THREAD {
                                    let key = xorshift(&mut rng) % HOT_KEYS;
                                    let mut entry = map.entry(key);
                                    if let Some(v) = entry.get_mut() {
                                        *v = v.wrapping_add(1);
                                    }
                                }
                            });
                        }
                    });
                })
            },
        );
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// LruLockMap
// ---------------------------------------------------------------------------

/// Concurrent read-only workload over a prefilled cache: `get` promotes the
/// entry in the LRU list, `peek` does not.
fn bench_lru_concurrent_read(c: &mut Criterion) {
    const KEYS: u64 = 1 << 15;
    let cache = LruLockMap::<u64, u64>::new(1 << 16);
    for i in 0..KEYS {
        cache.insert(i, i);
    }

    let mut group = c.benchmark_group("lru_concurrent_read");
    configure(&mut group);
    for &threads in THREAD_COUNTS {
        group.throughput(Throughput::Elements((threads * OPS_PER_THREAD) as u64));
        for (name, use_peek) in [("get", false), ("peek", true)] {
            group.bench_with_input(BenchmarkId::new(name, threads), &threads, |b, &threads| {
                b.iter(|| {
                    thread::scope(|s| {
                        for t in 0..threads {
                            let cache = &cache;
                            s.spawn(move || {
                                let mut rng = seed(t);
                                let mut sum = 0u64;
                                for _ in 0..OPS_PER_THREAD {
                                    let key = xorshift(&mut rng) % KEYS;
                                    let value = if use_peek {
                                        cache.peek(&key)
                                    } else {
                                        cache.get(&key)
                                    };
                                    if let Some(v) = value {
                                        sum = sum.wrapping_add(v);
                                    }
                                }
                                black_box(sum);
                            });
                        }
                    });
                })
            });
        }
    }
    group.finish();
}

/// Concurrent mixed workload with constant eviction pressure: the key space is
/// four times the cache capacity, so inserts continuously evict LRU entries.
fn bench_lru_concurrent_mixed_evict(c: &mut Criterion) {
    const KEYS: u64 = 1 << 16;
    let cache = LruLockMap::<u64, u64>::new(1 << 14);

    let mut group = c.benchmark_group("lru_concurrent_mixed_evict");
    configure(&mut group);
    for &threads in THREAD_COUNTS {
        group.throughput(Throughput::Elements((threads * OPS_PER_THREAD) as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(threads),
            &threads,
            |b, &threads| {
                b.iter(|| {
                    thread::scope(|s| {
                        for t in 0..threads {
                            let cache = &cache;
                            s.spawn(move || {
                                let mut rng = seed(t);
                                for _ in 0..OPS_PER_THREAD {
                                    let r = xorshift(&mut rng);
                                    let key = r % KEYS;
                                    if r % 2 == 0 {
                                        cache.insert(key, key);
                                    } else {
                                        black_box(cache.get(&key));
                                    }
                                }
                            });
                        }
                    });
                })
            },
        );
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_lockmap_insert,
    bench_lockmap_concurrent_get,
    bench_lockmap_concurrent_mixed,
    bench_lockmap_hot_key_entry,
    bench_lru_concurrent_read,
    bench_lru_concurrent_mixed_evict,
);
criterion_main!(benches);
