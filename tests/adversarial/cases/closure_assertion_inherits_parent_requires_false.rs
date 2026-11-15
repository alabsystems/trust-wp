//@ expect: reject
//@ mechanism: the typeck-root fallback in `prepare_proof_assert` reached three lookups, not one: the preconditions, the containing CONTRACT (from which `containing_requires_false` is read) and the parameter environment. A contracted closure with no `#[requires]` inside a `#[requires(false)]` function took the parent's `false` as its own precondition, and the parent's explicit `requires(false)` as licence to accept a vacuous assertion.
//@ accept-means: an assertion false for every capture is discharged in a closure whose own precondition is `true`, because the function that builds it can never be called.
//@ WHY THE ASSERTION IS FALSE: the closure's precondition is empty and nothing constrains the captured `x`; Creusot proves the assertion in the closure's own VC, not the parent's, and fails it. That the parent is uncallable is a fact about the parent.
//@ teeth: NOT a live false accept on the parent commit, measured: the fallback handed the closure the parent's `false`, and the vacuity check refused the assertion as `unknown (vacuous proof)`. What `fn-failed` pins is the environment: the assertion is now REFUTED with a counterexample in the closure's own, where the fallback could only make it vacuous. Its contract-free twin contractless_closure_assertion_in_uncallable_parent.rs is the spelling that was live.
//@ fixed-by: D-106
//@ fn-failed: parent::{closure#2}
//@ also-verified: parent
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(false)]
pub fn parent(x: u32) {
    let c = #[ensures(true)]
    move || {
        proof_assert!(x@ == 1000);
    };
    c()
}
