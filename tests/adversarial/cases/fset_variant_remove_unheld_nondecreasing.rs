//@ expect: reject
//@ mechanism: the FSet theory in a variant decrease query shortens a set by `remove` only for an
//@ mechanism: element the set holds (`contains(s, x) ==> len(remove(s, x)) == len(s) - 1`). Removing an
//@ mechanism: arbitrary `x` from a non-empty set need not shorten it, so the decrease is not owed.
//@ accept-means: termination is credited to a recursion that loops forever whenever `x` is not in
//@ accept-means: `s`, and its defining axiom is registered for every unfolding.
//@ WHY IT MUST BE REJECTED: Creusot's variant goal `len(remove(s, x)) < len(s)` is false at
//@ WHY IT MUST BE REJECTED: `s = {1}`, `x = 0`.
//@ teeth: UNVERIFIED for the FSet theory: rejected with and without it. The case pins the
//@ teeth: membership premise of the remove-length axiom.
//@ verdict: error
//@ refused-with: logic recursion check failed: `creusot_test::drain`: self-recursive logic function variant
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
pub fn drain(s: FSet<Int>, x: Int) -> Int {
    if s.is_empty() { 0 } else { drain(s.remove(x), x) }
}

pub fn uses_drain() {
    proof_assert! { drain(FSet::empty(), 0) == 0 };
}
