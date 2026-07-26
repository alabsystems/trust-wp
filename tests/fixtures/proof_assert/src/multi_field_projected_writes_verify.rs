#![allow(unexpected_cfgs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression for #1445: multi-field projected writes should both be visible.
//!
//! Writes to distinct fields of the same tuple (pair.0, pair.1) should produce
//! independent LetAssume facts, each visible at the proof_assert point.
//! Unlike contradictory same-field writes (tested in #1424), distinct-field
//! writes do not alias and both facts should be retained.

use trust_wp::proof_assert;

fn multi_field_projected_writes_verify() -> (i32, i32) {
    let mut pair = (0_i32, 0_i32);
    pair.0 = 1;
    pair.1 = 2;
    proof_assert!(pair.0@ == 1);
    pair
}

fn main() {
    multi_field_projected_writes_verify();
}
