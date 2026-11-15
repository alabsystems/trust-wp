//@ expect: verify
//@ xfail: the binder is carried by the unbounded integers (D-7), where two values of `U` differ, so the
//@ xfail: true claim is refuted; the isolating twin of
//@ xfail: quantifier_binder_unit_struct_cardinality_read_as_integers_granted.rs, OPEN.
//@ mechanism: control: `U` has one value, and `f` returns true.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `f FAILED ✗ (postcondition)` with D-206 in force)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct U;

#[ensures(result == (forall<a: U, b: U> a == b))]
pub fn f() -> bool {
    true
}
