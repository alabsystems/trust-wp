//@ expect: reject
//@ mechanism: a closure with no `#[requires]` of its own inherits the enclosing function's `#[requires]` for its assertions (the `fn_preconditions` fallback to the typeck root owner in `prepare_proof_assert`). An `FnMut` closure's captured state changes between calls, so a fact about the parent's parameter at the parent's entry says nothing about the captured place at a later call.
//@ accept-means: an assertion over mutable captured state that the closure's own first call falsifies is discharged by the parent's entry precondition, and the closure is credited.
//@ WHY THE ASSERTION IS FALSE: the first call sets the captured `x` to 3, so at the second call `x@ == 7` does not hold; the closure's precondition (none) cannot rule the second call out.
//@ teeth: MEASURED ACCEPTED, exit 0, both with D-87's fold and before it: the closure's assertion is `verified ✓` on the parent's precondition and `parent::{closure#2} verified ✓` follows. The write placed BEFORE the assertion in the same body is refuted, so the body walk sees the closure's own writes; only the state a previous call left behind is lost to the inherited entry fact.
//@ fixed-by: D-106 — `prepare_proof_assert` reads the preconditions, the contract and the parameter environment of the function whose MIR holds the assertion, and no longer falls back to the typeck root owner's
//@ fn-failed: parent::{closure#2}
//@ also-verified: parent
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 7)]
pub fn parent(mut x: u32) {
    let mut c = #[ensures(true)]
    || {
        proof_assert!(x@ == 7);
        x = 3;
    };
    c();
    c();
}
