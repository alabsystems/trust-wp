//@ expect: reject
//@ mechanism: a plain assignment to a field of a BY-VALUE struct parameter (`p.a = 7;`) never reaches the proof_assert lane's view of the parameter: the assertion reads `p.a` at its entry value, so the precondition about that entry value discharges a claim about the current one. No call and no borrow is involved. The function-level lane sees the same write: returning `p.a` under `#[ensures(result@ == 7)]` verifies, so only the assertion lane loses it. A by-value scalar parameter (`x = 7;`) and a whole-struct reassignment (`p = P { .. }`) do reach the lane, collide with the entry precondition read as a current fact, and are refused as a vacuous proof rather than credited.
//@ accept-means: an assertion about a parameter's field after the function overwrote that field is proved from the precondition on its entry value, and the crate exits 0.
//@ WHY THE ASSERTION IS FALSE: `p.a = 7` runs before the assertion, so `p.a` is 7 there, never 3.
//@ teeth: MEASURED ACCEPTED, exit 0: `proof_assert in creusot_test::k verified ✓` and `k verified ✓`. Without the `requires` the same assertion is refuted, and the TRUE `p.a@ == 7` is refuted with or without it (proof_assert_after_param_field_write_control.rs): the write is not modelled at all, the entry value stands in for the current one. A tuple parameter (`t.0 = 7;`) is accepted the same way.
//@ fixed-by: D-241: the walk binds the parameter written through a field to the functional update of its value, and its `#[requires]` speaks of its entry symbol, so the assertion reads the stored 7.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub a: u32,
    pub b: u32,
}

#[requires(p.a@ == 3)]
pub fn k(mut p: P) {
    p.a = 7;
    proof_assert!(p.a@ == 3);
}
