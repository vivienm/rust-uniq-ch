#![feature(test)]

extern crate test;

use test::Bencher;
use uniq_ch::Bjkst;

macro_rules! bench_len {
    ($name:ident, $n:expr) => {
        #[bench]
        fn $name(bencher: &mut Bencher) {
            let bjkst = Bjkst::<u32>::from_iter(1..$n);
            bencher.iter(|| bjkst.len());
        }
    };
}

bench_len!(len_1e6, 1_000_000);
