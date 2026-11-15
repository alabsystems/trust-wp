//@ expect: reject
//@ mechanism: a program function runs an annotated loop, then returns `None` and claims `result != None`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`), which gives the function-level check the value `result` is bound to after an annotated loop, reads the return with the syntax-only translator, which reads a field-less aggregate as the unit tuple, so the variant is lost; the datatype result binding (`trust-wp-ay` `verify::function::result_binding::assert_result_datatype_binding`) re-wraps the body in a constructor whenever a postcondition compares `result` with an `Option`/`Result` constructor (`encode_branch_as_datatype`), and the unit value is wrapped as `Some(..)`.
//@ fixed-by: D-165
//@ accept-means: a function that always returns `None` is credited with a postcondition saying it never does, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(n)` returns `None` for every `n`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip: `trust-wp: prog verified ✓`. At D-165: `trust-wp: prog FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result != None)]
pub fn prog(n: u32) -> Option<u32> {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    None
}
