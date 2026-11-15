//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then returns `succ(i)` and claims `result == n`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, reads any one-argument call whose destination has no debug name as the identity (a rule meant for `Ghost::new`), so `succ(i)` is read as `i`, which the loop leaves at `n`. The same holds of `succ(i) * 1` (the call's value in a temporary).
//@ fixed-by: D-165
//@ accept-means: a function that returns `n + 1` is credited with a postcondition saying it returns `n`, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0)` returns `succ(0)`, which is `1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: succ verified ✓`, `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog unknown (incomplete loop: no single post-loop return value)`.
//@ also-verified: succ
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x < 100)]
#[ensures(result == x + 1)]
pub fn succ(x: u32) -> u32 {
    x + 1
}

#[requires(n < 100)]
#[ensures(result == n)]
pub fn prog(n: u32) -> u32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    succ(i)
}
