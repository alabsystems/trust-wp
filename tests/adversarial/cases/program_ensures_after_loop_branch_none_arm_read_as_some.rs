//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then returns `None` on one branch and `Some(i)` on the other, and claims `result != None`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, follows one successor of every branch and returns the first `Return` it reaches, so the branch is read as its `Some(i)` arm alone.
//@ fixed-by: D-165
//@ accept-means: a function that returns `None` for some argument is credited with a postcondition saying it never does, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, true)` returns `None`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result != None)]
pub fn prog(n: u32, c: bool) -> Option<u32> {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    if c { None } else { Some(i) }
}
