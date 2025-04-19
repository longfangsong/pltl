use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fxhash::FxHashSet;
use pltl::utils::{BitSet, BitSet32};

fn create_test_data(size: usize) -> (FxHashSet<u32>, BitSet32) {
    let mut hashset = FxHashSet::default();
    let mut bitset = 0;
    for i in 0..size {
        hashset.insert(i as u32);
        bitset.set_bit(i as u32);
    }
    (hashset, bitset)
}

fn bench_iter(c: &mut Criterion) {
    for size in [2, 4, 8, 16, 32] {
        let (hashset, bitset) = create_test_data(size);
        let mut group = c.benchmark_group(format!("iter_size_{}", size));

        group.bench_function("hashset_iter", |b| {
            b.iter(|| {
                for i in black_box(&hashset) {
                    black_box(i);
                }
            })
        });

        group.bench_function("bitset_iter", |b| {
            b.iter(|| {
                for i in black_box(&bitset).iter() {
                    black_box(i);
                }
            })
        });

        group.finish();
    }
}

fn bench_contains(c: &mut Criterion) {
    for size in [2, 4, 8, 16, 32] {
        let (hashset, bitset) = create_test_data(size);
        let mut group = c.benchmark_group(format!("contains_size_{}", size));

        group.bench_function("hashset_contains", |b| {
            b.iter(|| black_box(&hashset).contains(&1))
        });

        group.bench_function("bitset_contains", |b| {
            b.iter(|| black_box(&bitset).contains(1))
        });

        group.finish();
    }
}

criterion_group!(benches, bench_iter, bench_contains);
criterion_main!(benches);
