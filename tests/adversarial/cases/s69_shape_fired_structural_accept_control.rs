//@ expect: verify
//@ mechanism: control for `s69_shape_fired_structural_accept`. The fix restores the structural accept lanes' UNREACHABILITY after a refutation shape fires; it must not disturb them when NO shape fires. Same recursive logic fn, same `recursive_logic_fn_equality_matches_evaluation` lane, no `#[requires]` at all, and the postcondition is the TRUE evaluation (`fact(3) == 6`) — so no shape can fire and the lane must still discharge it.
//@ teeth: a regression that made a fired shape's `break` unconditional, or that made `prove_prechecked_literal_false_obligation_with_solver` refuse outright, turns this control into an OVER-REFUSAL.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
#[variant(n)]
#[requires(n >= 0)]
pub fn fact(n: Int) -> Int {
    pearlite! { if n <= 0 { 1 } else { n * fact(n - 1) } }
}

#[ensures(fact(3) == 6)]
pub fn ok3(x: i32) -> i32 {
    x
}
