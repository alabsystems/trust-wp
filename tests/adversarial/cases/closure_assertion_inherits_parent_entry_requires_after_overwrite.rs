//@ expect: reject
//@ mechanism: a closure with no `#[requires]` of its own inherits the enclosing function's `#[requires]` for its assertions (the `fn_preconditions` fallback to the typeck root owner in `prepare_proof_assert`). The parent's precondition is a fact about its parameters at ENTRY; the closure captures the parameter's value at the capture point, after the parent overwrote it, and the inherited clause is read as a fact about that captured value.
//@ accept-means: the closure's assertion about a captured value the parent had already overwritten is discharged by the parent's entry precondition, and the closure is credited.
//@ WHY THE ASSERTION IS FALSE: `x` is 3 when the `move` closure captures it; the parent's `x@ == 7` held only before `x = 3`.
//@ teeth: MEASURED ACCEPTED, exit 0, both with D-87's fold and before it: the closure's assertion is `verified ✓` on the parent's precondition and `parent::{closure#2} verified ✓` follows. Without the overwrite the same assertion is true. Not a shadowing defect: the closure has no parameter at all, so a fix that only renames shadowed parameters leaves this RED.
//@ fixed-by: D-106 — `prepare_proof_assert` reads the preconditions, the contract and the parameter environment of the function whose MIR holds the assertion, and no longer falls back to the typeck root owner's
//@ fn-failed: parent::{closure#2}
//@ also-verified: parent
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 7)]
#[ensures(result@ == 3)]
pub fn parent(mut x: u32) -> u32 {
    x = 3;
    let c = #[ensures(result@ == 3)]
    move || {
        proof_assert!(x@ == 7);
        3u32
    };
    c()
}
