//@ expect: reject
//@ mechanism: the SECOND call of a closure must check its precondition in the state that call
//@ mechanism: starts from. `x@ == 999_999` holds before the first `c()`; the closure's own
//@ mechanism: postcondition makes `x@ == 1_000_000` before the second, which violates its
//@ mechanism: `requires(x@ < 1_000_000)`. A capture name left unsubstituted resolved to the
//@ mechanism: caller's variable, so both preconditions were checked against the pre-first-call
//@ mechanism: state.
//@ fixed-by: s44 v2 (wp-s44): a closure call's precondition reads its captures in the pre-call state
//@ accept-means: `f` credited although its second `c()` calls the closure outside its precondition.
//@ verdict: failed
//@ fn-failed: f
//@ teeth: measured on the review probe r_closure_chain: `trust-wp: f verified ✓` on the campaign
//@ teeth: base (the run only ended non-zero because the closure body itself is incomplete);
//@ teeth: `trust-wp: f FAILED ✗ (postcondition)` on wp-s44.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x@ == 999_999u32@)]
pub fn f(mut x: u32) {
    let mut c = #[requires(x@ < 1_000_000)]
    #[ensures((^x)@ == x@ + 1)]
    || {
        x += 1
    };
    c();
    c();
}
