#![feature(test)]

extern crate test;

use test::Bencher;
use uniq_ch::Bjkst;

macro_rules! bench_insert {
    ($name:ident, $n:expr) => {
        #[bench]
        fn $name(bencher: &mut Bencher) {
            bencher.iter(|| {
                Bjkst::<u32>::from_iter(1..$n);
            });
        }
    };
}

bench_insert!(insert_1e3, 1_000);

bench_insert!(insert_1e6, 1_000_000);
