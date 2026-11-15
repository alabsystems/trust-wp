//@ expect: verify
//@ mechanism: control for program_ensures_err_after_loop_read_as_ok, with the postcondition the body meets: `Err(i)` after an annotated loop is `Err`. FAILED with a counterexample at the campaign tip, where the post-loop walk read `Err(i)` as `i` and the datatype binding wrapped it as `Ok(i)`.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(match result { Ok(_) => false, Err(_) => true })]
pub fn prog(n: u32) -> Result<u32, u32> {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    Err(i)
}
