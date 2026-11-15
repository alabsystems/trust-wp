//@ expect: reject
//@ mechanism: a logic function's variant decrease query is proved with the encoder's FSet theory
//@ mechanism: (`len`, `insert`, `remove`, `peek`, `is_empty` linked through membership, declared
//@ mechanism: whether or not the query names `contains`). That theory must not prove a decrease the
//@ mechanism: recursion does not make: inserting into a non-empty set keeps or grows its length.
//@ accept-means: a `#[logic]` fn whose recursion never terminates is registered with its defining
//@ accept-means: axiom `!is_empty(s) -> climb(s) = climb(insert(s, 0)) + 1`, which at a set holding
//@ accept-means: `0` states `climb(s) = climb(s) + 1`.
//@ WHY IT MUST BE REJECTED: Creusot's variant goal `len(insert(s, 0)) < len(s)` is false at every
//@ WHY IT MUST BE REJECTED: non-empty `s`.
//@ teeth: UNVERIFIED for the FSet theory: rejected with and without it (without it every FSet
//@ teeth: variant query failed on uninterpreted symbols). The case pins that the theory, once
//@ teeth: added, does not prove a non-decrease: the query ends `unknown` and the refusal stands.
//@ verdict: error
//@ refused-with: logic recursion check failed: `creusot_test::climb`: self-recursive logic function variant
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{
    logic::{FSet, Int},
    prelude::*,
};

#[logic(open)]
#[variant(s.len())]
pub fn climb(s: FSet<Int>) -> Int {
    if s.is_empty() { 0 } else { climb(s.insert(0)) + 1 }
}

pub fn uses_climb() {
    proof_assert! { climb(FSet::empty()) == 0 };
}
