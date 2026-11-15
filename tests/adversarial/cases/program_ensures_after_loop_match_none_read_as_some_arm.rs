//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then matches its `Option<u32>` parameter, returning `1` for `Some` and `0` for `None`; it requires `o == None` and claims `result == 1`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, follows one successor of the discriminant switch, so the match is read as its `Some` arm whatever the parameter is.
//@ fixed-by: D-165
//@ accept-means: a function called only with `None` returns `0`, and is credited with a postcondition saying it returns `1`; the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, None)` returns `0`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(o == None)]
#[ensures(result == 1u32)]
pub fn prog(n: u32, o: Option<u32>) -> u32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    match o {
        Some(_) => 1,
        None => 0,
    }
}
