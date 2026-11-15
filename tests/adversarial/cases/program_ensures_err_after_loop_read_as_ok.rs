//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then returns `Err(i)` and claims the result is `Ok`. The post-loop walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`) reads the return with the syntax-only translator, which reads a one-field aggregate as its field, so `Err(i)` is extracted as `i`; the datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) then wraps that bare `i` in the default constructor, `Ok`, and `result` is read as `Ok(i)`. The same reading makes `ensures(match result { Ok(_) => false, Err(_) => true })` of the same body FAIL with a counterexample.
//@ fixed-by: D-165
//@ accept-means: a function that always returns `Err` is credited with a postcondition saying it returns `Ok`, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(n)` returns `Err(n)` for every `n`, which the `Err(_) => false` arm matches.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(match result { Ok(_) => true, Err(_) => false })]
pub fn prog(n: u32) -> Result<u32, u32> {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    Err(i)
}
