//@ expect: verify
//@ mechanism: control for program_ensures_none_after_loop_read_as_some, with the postcondition the body meets: `None` after an annotated loop is `None`. FAILED with a counterexample at the campaign tip, where the post-loop walk read `None` as the unit value and the datatype binding wrapped it as `Some`.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == None)]
pub fn prog(n: u32) -> Option<u32> {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    None
}
