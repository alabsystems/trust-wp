//@ expect: verify
//@ xfail: the elided binder `x`, which rustc types `u8` from `is300`'s parameter, is read over the
//@ xfail: unbounded integers (D-205, not changed), where `x == 300` refutes the claim that no `x`
//@ xfail: satisfies `is300`. The isolating twin of
//@ xfail: quantifier_binder_elided_inferred_machine_int_read_unbounded.rs.
//@ mechanism: control: no `u8` is 300, and `f` returns false.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `f FAILED ✗ (postcondition)` with D-205 in force)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn is300(x: u8) -> bool {
    pearlite! { x@ == 300 }
}

#[ensures(result == (exists<x> is300(x)))]
pub fn f() -> bool {
    false
}
