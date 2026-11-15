//@ expect: reject
//@ mechanism: the variant grammar admits a length/cardinality call as an Int-sorted variant
//@ mechanism: term; if the decrease obligation were not owed on that term kind, a recursion
//@ mechanism: that GROWS the measured sequence would still be credited as terminating.
//@ fixed-by: the term kind is admitted by a result-sort judgement only — the same
//@ fixed-by: `prove_self_variant_decrease` goal pair `0 <= before` / `after < before` is owed
//@ fixed-by: on it, and it is refutable here at any non-empty `c`.
//@ accept-means: a `#[logic]` fn whose defining axiom has no well-founded justification is
//@ accept-means: registered, so every unfolding of it is credited; `grow` is defined by
//@ accept-means: `len(c) != 0 -> grow(c) = grow(push_back(c, 0))`, an equation with no least
//@ accept-means: fixed point, and the assertion is discharged from it.
//@ teeth: VERIFIED by knob (ii) — an early `SelfVariantDecrease::Proven` return in
//@ teeth: `try_prove_self_variant_decrease` makes this case ACCEPT (exit 0, the proof_assert
//@ teeth: verified) on this same build; the control verifies in both arms.
//@ verdict: error
//@ refused-with: variant `c.len()` does not strictly decrease at self-call creusot_test::grow -> creusot_test::grow
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{
    logic::{Int, Seq},
    prelude::*,
};

#[logic(open)]
#[variant(c.len())]
pub fn grow(c: Seq<Int>) -> Int {
    if c.len() == 0 { 0 } else { grow(c.push_back(0)) }
}

pub fn uses_grow() {
    proof_assert! { grow(Seq::empty()) == 0 };
}
