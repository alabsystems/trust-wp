//@ expect: reject
//@ mechanism: `prepare_proof_assert` takes the preconditions of an assertion's containing function from `fn_preconditions`, and a closure with no `#[requires]` of its own has no entry there, so the lookup falls back to the TYPECK ROOT OWNER's (the enclosing function's) `#[requires]`. Those clauses are written over the parent's parameters and hold at the parent's entry; handed to the closure's assertion they are resolved against the closure's own names, so a closure parameter that shadows a parent parameter is assumed to satisfy the parent's precondition.
//@ mechanism: The closure's contract lane proves the closure against its own (empty) precondition; the assertion lane proves the closure's assertion against the parent's. Since D-87 the closure's credit is settled on that assertion verdict, so the grant and the obligation come from two different environments.
//@ accept-means: the closure's assertion, false at the only call (`c(3)`), is discharged by the parent's `x@ == 7` about a different variable, and the closure is credited.
//@ WHY THE ASSERTION IS FALSE: the closure's `x` is its own argument, which is 3 at the call; nothing in the closure's (empty) precondition constrains it. Creusot puts the assertion in the closure's own VC, whose precondition is the closure's `requires` alone.
//@ teeth: MEASURED ACCEPTED, exit 0, both with D-87's fold and before it: the closure's assertion is `verified ✓` with the parent's `x@ == 7` counted among its contract preconditions, and `parent::{closure#2} verified ✓` follows. The same closure given an explicit `#[requires(true)]` has an entry of its own, and its assertion is refuted and the closure FAILED: the fallback is the whole difference. The closure's contract lane does not inherit: `#[ensures(result@ == 7)]` on the same closure is refuted.
//@ fixed-by: D-106 — `prepare_proof_assert` reads the preconditions, the contract and the parameter environment of the function whose MIR holds the assertion, and no longer falls back to the typeck root owner's
//@ fn-failed: parent::{closure#2}
//@ also-verified: parent
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 7)]
#[ensures(result@ == 8)]
pub fn parent(x: u32) -> u32 {
    let c = #[ensures(result@ == x@)]
    |x: u32| {
        proof_assert!(x@ == 7);
        x
    };
    let _ = c(3);
    x + 1
}
