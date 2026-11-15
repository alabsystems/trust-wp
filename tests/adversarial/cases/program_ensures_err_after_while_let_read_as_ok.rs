//@ expect: reject
//@ mechanism: the `while let` spelling of program_ensures_err_after_loop_read_as_ok.rs: a program function drains a vector with `while let Some(_) = v.pop()`, then returns `Err(0)` and claims the result is `Ok`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, reads `Err(0)` as its field `0`, and the datatype result binding wraps that in the default constructor, `Ok`.
//@ fixed-by: D-165
//@ accept-means: a function that always returns `Err` is credited with a postcondition saying it returns `Ok`, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(v)` returns `Err(0)` for every `v`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(match result { Ok(_) => true, Err(_) => false })]
pub fn prog(v: &mut Vec<u32>) -> Result<u32, u32> {
    #[invariant(true)]
    while let Some(_x) = v.pop() {}
    Err(0)
}
