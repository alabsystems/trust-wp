//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then matches its `Result` parameter, returning `1` for `Ok` and `0` for `Err`; it requires the parameter to be `Ok` and claims `result == 0`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, follows one successor of the discriminant switch, so the match is read as its `Err` arm whatever the parameter is.
//@ fixed-by: D-165
//@ accept-means: a function called only with `Ok` returns `1`, and is credited with a postcondition saying it returns `0`; the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, Ok(0))` returns `1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(match r { Ok(_) => true, Err(_) => false })]
#[ensures(result == 0u32)]
pub fn prog(n: u32, r: Result<u32, u32>) -> u32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    match r {
        Ok(_) => 1,
        Err(_) => 0,
    }
}
