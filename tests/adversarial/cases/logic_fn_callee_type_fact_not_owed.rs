//@ expect: reject
//@ mechanism: twin of logic_fn_callee_type_fact_not_owed_control: owing only the written `requires` still owes them, beside the machine-integer ranges discovery appends.
//@ accept-means: the written precondition of a callee with appended type facts is never owed.
//@ WHY IT IS FALSE: `caller` calls `g(-1, k)`, and `g` requires `n >= 0`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `creusot_test::caller verified ✓`, the call never examined.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(n >= 0)]
#[variant(n)]
pub fn g(n: Int, k: u32) -> Int {
    pearlite! { n + k@ }
}

#[logic]
#[ensures(true)]
pub fn caller(k: u32) -> Int {
    g(-1, k)
}
