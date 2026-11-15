//@ expect: verify
//@ mechanism: control for logic_fn_requires_only_credited_by_its_assertion, differing in the caller's `#[requires]` alone: a logic function with no `ensures` owes its assertions and its callees' preconditions, both hold, and it is credited on them.
//@ accept-means: n/a (control) — `y > 0` puts the call inside `needs_pos`'s precondition, and the assertion is `true`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[requires(y > 0)]
pub fn caller(y: Int) -> Int {
    proof_assert!(true);
    needs_pos(y)
}
