//@ expect: reject
//@ mechanism: a program function builds a tuple `(0, 0)`, runs an annotated loop, writes `7` into its first field and returns that field, claiming `result == 0`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, follows whole-local assignments only, so the field write is not seen and the tuple keeps its value from before the loop.
//@ fixed-by: D-165
//@ accept-means: a function that returns `7` is credited with a postcondition saying it returns `0`, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(n)` returns `7`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog unknown (quantifier-ematching-exists-incomplete)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn prog(n: u32) -> u32 {
    let mut t = (0u32, 0u32);
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    t.0 = 7;
    t.0
}
