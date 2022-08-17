#![feature(test)]

extern crate test;

use test::Bencher;
use uniq_ch::Bjkst;

#[bench]
fn insert_10k(bench: &mut Bencher) {
    bench.iter(|| {
        let mut uniq: Bjkst<usize> = Bjkst::new();

        for i in 1..=10_000 {
            uniq.insert(&i);
        }
    })
}
