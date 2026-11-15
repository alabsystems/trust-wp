//@ expect: verify
//@ mechanism: control for logic_fn_std_unreachable_reached, differing in the caller's `#[requires]` alone: `unreachable()` sits in an arm the precondition excludes, so the `false` it owes is owed nowhere.
//@ accept-means: n/a (control) — the arm that calls `unreachable()` is never taken.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn caller(x: Int) -> Int {
    proof_assert!(true);
    if x > 0 { 0 } else { creusot_std::logic::unreachable() }
}
