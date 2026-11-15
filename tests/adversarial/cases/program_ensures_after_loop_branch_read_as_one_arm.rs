//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then returns `0` on one branch and `1` on the other, and claims `result == 0`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, follows one successor of every branch and returns the first `Return` it reaches, so `result` is bound to the `0` arm alone. No datatype is involved: every function whose post-loop code branches is read so.
//@ fixed-by: D-165
//@ accept-means: a function that returns `1` for some arguments is credited with a postcondition saying it always returns `0`, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, false)` returns `1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn prog(n: u32, c: bool) -> u32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    if c { 0 } else { 1 }
}
