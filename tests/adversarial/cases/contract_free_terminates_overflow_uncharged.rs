//@ expect: reject
//@ verdict: failed
//@ fn-failed: hop
//@ mechanism: a clause-free `#[check(terminates)]` body whose only goal is a machine-integer
//@ mechanism: overflow assert. Discovery admits it by its `terminates` marker, and then the
//@ mechanism: extraction gate refuses to extract a clause-free contract unless some body predicate
//@ mechanism: says it owes a goal — and the arithmetic predicate excludes every item carrying a
//@ mechanism: `trust-wp:` doc marker, which `trust-wp:check:terminates` is, while the abort /
//@ mechanism: callee-precondition predicate did not read `Assert` terminators at all. Admitted by
//@ mechanism: one predicate and refused by the other: a target of nothing, the D-71 shape.
//@ accept-means: `hop(u32::MAX)` panics with "attempt to add with overflow" and the crate reported
//@ accept-means: a clean verification run with `hop` named in no verdict line
//@ fixed-by: D-95
//@ teeth: ACCEPTED (exit 0, `hop` named in no verdict line) before D-95; the same body without
//@ teeth: `#[check(terminates)]` was refuted, and the same body with its addition guarded by
//@ teeth: `a < 10` verifies with the marker (the extraction is not a blanket refusal).
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

#[check(terminates)]
pub fn hop(a: u32) -> u32 {
    a + 1
}
