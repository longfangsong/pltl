use bimap::BiHashMap;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fxhash::{FxBuildHasher, FxHashMap};
use std::collections::HashMap;

fn bench_vec_position(vec: &Vec<String>, needle: &str) -> Option<usize> {
    vec.iter().position(|x| x == needle)
}

fn bench_vec_position_rev(vec: &Vec<String>, needle: usize) -> Option<String> {
    vec.get(needle).cloned()
}

fn bench_hashmap_get(map: &FxHashMap<String, usize>, needle: &str) -> Option<usize> {
    map.get(needle).cloned()
}

fn bench_std_hashmap_get(map: &HashMap<String, usize>, needle: &str) -> Option<usize> {
    map.get(needle).cloned()
}

fn bench_bimap_get_by_left(
    map: &BiHashMap<String, usize, FxBuildHasher, FxBuildHasher>,
    needle: &str,
) -> Option<usize> {
    map.get_by_left(needle).cloned()
}

fn bench_bimap_get_by_right(
    map: &BiHashMap<String, usize, FxBuildHasher, FxBuildHasher>,
    needle: usize,
) -> Option<String> {
    map.get_by_right(&needle).cloned()
}

fn create_test_data(
    size: usize,
) -> (
    Vec<String>,
    FxHashMap<String, usize>,
    HashMap<String, usize>,
    BiHashMap<String, usize, FxBuildHasher, FxBuildHasher>,
) {
    let vec: Vec<String> = (0..size).map(|i| format!("{}", i)).collect();
    let fx_map: FxHashMap<String, usize> = vec
        .iter()
        .enumerate()
        .map(|(i, s)| (s.clone(), i))
        .collect();
    let std_map: HashMap<String, usize> = vec
        .iter()
        .enumerate()
        .map(|(i, s)| (s.clone(), i))
        .collect();
    let mut bimap: BiHashMap<String, usize, FxBuildHasher, FxBuildHasher> =
        BiHashMap::with_hashers(FxBuildHasher::default(), FxBuildHasher::default());
    for (i, s) in vec.iter().enumerate() {
        bimap.insert(s.clone(), i);
    }
    (vec, fx_map, std_map, bimap)
}

fn compare_lookup(c: &mut Criterion) {
    for size in [2, 4, 8, 16] {
        let (vec, fx_map, std_map, bimap) = create_test_data(size);

        // 正向查找测试
        let needle_in = "1";
        let mut group = c.benchmark_group(format!("lookup_size_{}_in", size));

        group.bench_function("vec_position", |b| {
            b.iter(|| bench_vec_position(black_box(&vec), black_box(needle_in)))
        });

        group.bench_function("fx_hashmap_get", |b| {
            b.iter(|| bench_hashmap_get(black_box(&fx_map), black_box(needle_in)))
        });

        group.bench_function("std_hashmap_get", |b| {
            b.iter(|| bench_std_hashmap_get(black_box(&std_map), black_box(needle_in)))
        });

        group.bench_function("bimap_get_by_left", |b| {
            b.iter(|| bench_bimap_get_by_left(black_box(&bimap), black_box(needle_in)))
        });

        group.finish();

        // 反向查找测试
        let needle_idx = 1;
        let mut group = c.benchmark_group(format!("reverse_lookup_size_{}_in", size));

        group.bench_function("vec_index", |b| {
            b.iter(|| bench_vec_position_rev(black_box(&vec), black_box(needle_idx)))
        });

        group.bench_function("bimap_get_by_right", |b| {
            b.iter(|| bench_bimap_get_by_right(black_box(&bimap), black_box(needle_idx)))
        });

        group.finish();

        // 不存在元素的查找测试
        let needle_not_in = format!("{}", size + 1);
        let mut group = c.benchmark_group(format!("lookup_size_{}_not_in", size));

        group.bench_function("vec_position", |b| {
            b.iter(|| bench_vec_position(black_box(&vec), black_box(&needle_not_in)))
        });

        group.bench_function("fx_hashmap_get", |b| {
            b.iter(|| bench_hashmap_get(black_box(&fx_map), black_box(&needle_not_in)))
        });

        group.bench_function("std_hashmap_get", |b| {
            b.iter(|| bench_std_hashmap_get(black_box(&std_map), black_box(&needle_not_in)))
        });

        group.bench_function("bimap_get_by_left", |b| {
            b.iter(|| bench_bimap_get_by_left(black_box(&bimap), black_box(&needle_not_in)))
        });

        group.finish();
    }
}

criterion_group!(benches, compare_lookup);
criterion_main!(benches);
