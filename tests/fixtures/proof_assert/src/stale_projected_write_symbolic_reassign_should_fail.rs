#![allow(unexpected_cfgs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression for #1450: non-constant whole-local reassignment must clear stale
//! projected-write facts.
//!
//! Unlike `projected_write_then_whole_reassign_should_fail` which uses constant
//! tuples (where the soundness gap is masked by constant folding), this fixture
//! uses a function parameter so the reassignment value is NOT constant-foldable.
//!
//! Sequence:
//! - `pair.1 = 10` introduces projected-write fact `tuple_get_1(pair) == 10`
//! - `pair = new_val` overwrites the entire local with a symbolic value
//!
//! Without the #1450 fix, the stale fact could survive and pair.1@ could
//! evaluate to the same symbolic variable referenced in the stale assumption,
//! producing vacuous verification. With the fix, facts are cleared on
//! whole-local reassignment, so the assertion correctly fails.

use trust_wp::proof_assert;

fn stale_projected_write_symbolic_reassign(new_val: (i32, i32)) {
    let mut pair = (0_i32, 0_i32);
    pair.1 = 10;
    pair = new_val;

    // Stale fact `tuple_get_1(pair) == 10` must NOT survive the whole-local
    // reassignment. After `pair = new_val`, pair.1 is new_val.1, not 10.
    proof_assert!(pair.1@ == 10);
    let _ = pair;
}

fn main() {
    stale_projected_write_symbolic_reassign((7, 20));
}
