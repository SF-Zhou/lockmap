use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use lockmap::*;

fn criterion_benchmark(c: &mut Criterion) {
    let count = 1 << 20;
    c.bench_with_input(
        BenchmarkId::new("insert_into_lockmap", count),
        &count,
        |b, &count| {
            b.iter(|| {
                let map = LockMap::with_capacity_and_shard_amount(1 << 15, 256);
                for i in 0..count {
                    map.insert(i, i);
                }
            })
        },
    );
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
