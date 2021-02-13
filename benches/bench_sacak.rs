use criterion::{criterion_group, criterion_main, Criterion};
use rand::{prelude::*, SeedableRng};

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut input = vec![];
    let mut rng = SmallRng::seed_from_u64(123);
    for i in 1..=6 {
        let mut s = vec![0u8; 10usize.pow(i as u32) - 1];

        for e in s.iter_mut() {
            *e = rng.gen_range(1u8..=u8::MAX);
        }

        s.push(0);
        input.push(s);
    }

    for s in input {
        let mut sa = vec![0u32; s.len()];
        c.bench_function(&format!("sacak {}", s.len()), |b| {
            b.iter(|| sacak::construct(&s, &mut sa))
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
