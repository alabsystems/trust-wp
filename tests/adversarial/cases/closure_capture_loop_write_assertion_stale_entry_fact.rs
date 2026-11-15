//@ expect: reject
//@ mechanism: a closure's captures live in its environment argument `_1`, which has no source parameter name, so D-38's guard could report the loop's write to it under no name at all and dropped nothing: the closure's `#[requires(x@ == 7)]` about the capture survived a loop that overwrote it. An environment the loop writes now stales every entry fact.
//@ accept-means: an assertion about a captured variable after a loop in the closure overwrote it is discharged by the closure's entry precondition.
//@ WHY THE ASSERTION IS FALSE: the loop body runs once and sets the captured `x` to 3.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: the assertion `verified ✓` and `parent::{closure#0} verified ✓`.
//@ fixed-by: D-106 — an invalidated closure environment is `InvalidatedEntryNames::unnamed`; since
//@ fixed-by: D-185 the assertion is refused before that, as a stale read of the capture the loop writes
//@ verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn parent() {
    let mut x = 7u32;
    let mut c = #[requires(x@ == 7)]
    #[ensures(true)]
    || {
        let mut i = 0u32;
        #[invariant(i@ <= 1)]
        while i < 1 {
            x = 3;
            i += 1;
        }
        proof_assert!(x@ == 7);
    };
    let _ = &mut c;
}
