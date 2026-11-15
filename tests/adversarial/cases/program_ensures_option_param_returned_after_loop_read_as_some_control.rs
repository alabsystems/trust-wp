//@ expect: verify
//@ mechanism: control for program_ensures_option_param_returned_after_loop_read_as_some, differing in `#[requires(o != None)]` alone.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(o != None)]
#[ensures(result != None)]
pub fn prog(n: u32, o: Option<u32>) -> Option<u32> {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    o
}
