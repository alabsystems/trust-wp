// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unsoundness regression tests for `produces` encoding.

use ntest::timeout;

use super::helpers::*;
use crate::{
    encoder::unsoundness::{self, UnsoundnessCategory},
    AYEncoder,
};

#[test]
#[timeout(30000)]
fn test_produces_ground_transitivity_does_not_demote_valid_state_sorts() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let mut encoder = AYEncoder::new_with_quantifiers();

    let ab = view(var("ab"));
    let bc = view(var("bc"));
    let p_ab = method_call(var("a"), "produces", vec![ab, var("b")]);
    let p_bc = method_call(var("b"), "produces", vec![bc, var("c")]);

    encoder.register_sort_hints(&[p_ab.clone(), p_bc.clone()]);
    encoder
        .encode_pure(&p_ab)
        .expect("first produces call should encode");
    encoder
        .encode_pure(&p_bc)
        .expect("second produces call should encode");

    let delta = unsoundness::delta(&before, &unsoundness::snapshot());
    assert_eq!(
        delta.get(&UnsoundnessCategory::SortFallbackToInt),
        None,
        "valid produces signatures should use the verified state sort instead of demoting"
    );

    unsoundness::reset();
}
