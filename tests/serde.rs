#![cfg(feature = "serde")]

use std::assert_eq;

use highway::HighwayBuildHasher;
use uniq_ch::Bjkst;

const SERIALIZED: &'static str = "[4,4,16,0,false,[null,6120665149970903695,null,null,null,null,\
                                  14520555826795478172,793563473396344097,null,null,null,null,\
                                  16707926894801950140,null,null,null]]";

#[test]
fn serialize() {
    let bjkst = Bjkst::<u32, HighwayBuildHasher>::from_iter([1, 2, 3, 4]);
    let serialized = serde_json::to_string(&bjkst).unwrap();
    assert_eq!(serialized, SERIALIZED);
}

#[test]
fn deserialize() {
    let mut bjkst: Bjkst<u32, HighwayBuildHasher> = serde_json::from_str(SERIALIZED).unwrap();
    assert_eq!(bjkst.len(), 4);

    // Insert an element already present in the BJKST. The count should not change.
    bjkst.insert(&4);
    assert_eq!(bjkst.len(), 4);

    // Insert a new element. The count should change.
    bjkst.insert(&5);
    assert_eq!(bjkst.len(), 5);
}
