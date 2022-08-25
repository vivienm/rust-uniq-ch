# uniq-ch

A Rust library for counting distinct elements in a stream,
using [ClickHouse uniq][ClickHouseRefUniq] data structure.

This uses [BJKST][BarYossef+02], a probabilistic algorithm that relies on
adaptive sampling and provides fast, accurate and deterministic results.
Two BJKSTs can be merged, making the data structure well suited for map-reduce
settings.

[Repository] | [Documentation]

[ClickHouseRefUniq]: <https://clickhouse.com/docs/en/sql-reference/aggregate-functions/reference/uniq/>
[BarYossef+02]: https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.12.6276
[Repository]: https://github.com/vivienm/rust-uniq-ch
[Documentation]: https://vivienm.github.io/rust-uniq-ch/uniq_ch/

## Examples

```rust
use uniq_ch::Bjkst;

let mut bjkst = Bjkst::new();

// Add some elements, with duplicates.
bjkst.extend(0..75_000);
bjkst.extend(25_000..100_000);

// Count the distinct elements.
assert!((99_000..101_000).contains(&bjkst.len()));
```
