//@ expect: verify
//@ xfail: the binder's range is stated on `*q` and `^q` (D-204). ay finds the negated goal
//@ xfail: unsatisfiable and withholds that answer: its terminal derivation is not trust-free
//@ xfail: (`inc_exists unknown (proof-trusted)`, through ay's substitution bridge). Without the range
//@ xfail: the goal read `q` over the unbounded integers
//@ xfail: (quantifier_binder_reference_to_machine_int_read_unbounded_granted.rs).
//@ mechanism: control: a quantified `&mut i32` equal to `n` witnesses the increment `inc_exists` makes.
//@ mechanism: The D-109 reading of a quantified borrow is guarded over a `bool` borrow in
//@ mechanism: v11_final_denotation_controls.rs, where no range is stated.
//@ fixed-by: n/a (control; verifying it needs a trust-free certificate for the ranged goal)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; verified before D-203, refused with D-203, unknown with D-204)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(*n < 100i32)]
#[ensures(exists<q: &mut i32> q == n && ^q == *q + 1i32)]
pub fn inc_exists(n: &mut i32) {
    *n += 1;
}
