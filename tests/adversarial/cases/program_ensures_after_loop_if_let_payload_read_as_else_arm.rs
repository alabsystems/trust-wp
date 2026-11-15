//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then returns the payload of its `Option<u32>` parameter under `if let Some(x)` and `0` otherwise; it requires `o == Some(5)` and claims `result == 0`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, follows one successor of the discriminant switch, so the `if let` is read as its `else` arm.
//@ fixed-by: D-165
//@ accept-means: a function called only with `Some(5)` returns `5`, and is credited with a postcondition saying it returns `0`; the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, Some(5))` returns `5`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(o == Some(5u32))]
#[ensures(result == 0u32)]
pub fn prog(n: u32, o: Option<u32>) -> u32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    if let Some(x) = o { x } else { 0 }
}
