//@ expect: reject
//@ mechanism: the assertion sink of f64_rem_assign_reads_param_as_unchanged.rs: a float `%` left
//@ mechanism: untranslated leaves `a` bound to its entry symbol after `a %= 0.5`, so `proof_assert!(a == 1.0)`
//@ mechanism: is proved from the precondition about the entry value. With `%` translated the assertion
//@ mechanism: lane still reads the entry precondition as a fact about the reassigned `a` and ay answers
//@ mechanism: `unsat`; the vacuity guard proof_assert_after_param_field_write_keeps_entry_requires.rs names
//@ mechanism: for a by-value scalar withholds that credit, exactly as it does for the integer `a %= 1`.
//@ accept-means: `rem_assert(1.0)` reaches the assertion with `a` equal to `0.0`; an accept claims it is `1.0`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED while D-215 left `%` untranslated (`proof_assert in creusot_test::rem_assert verified`);
//@ teeth: `unknown` on the campaign tip before D-215, which translated the remainder over the reals;
//@ teeth: `unknown` with `%` an uninterpreted function, withheld as lacking strict proof authority.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a == 1.0)]
#[ensures(true)]
pub fn rem_assert(mut a: f64) {
    a %= 0.5;
    proof_assert!(a == 1.0);
}
