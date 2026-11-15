//@ expect: reject
//@ mechanism: a program function sets a local to `0`, runs an annotated loop, assigns the local from a call returning `1` and returns it, claiming `result == 0`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, keeps a local at its old value when it cannot translate the new one, and it cannot translate a call's result, so the local keeps the value it had before the loop.
//@ fixed-by: D-165
//@ accept-means: a function that returns `1` is credited with a postcondition saying it returns `0`, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(n)` returns `one()`, which is `1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: one verified ✓`, `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog unknown (incomplete loop: no single post-loop return value)`.
//@ also-verified: one
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 1u32)]
pub fn one() -> u32 {
    1
}

#[ensures(result == 0u32)]
pub fn prog(n: u32) -> u32 {
    let mut x = 0u32;
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    x = one();
    x
}
