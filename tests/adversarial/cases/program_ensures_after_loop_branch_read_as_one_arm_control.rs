//@ expect: verify
//@ mechanism: control for program_ensures_after_loop_branch_read_as_one_arm: a postcondition both arms of the post-loop branch meet.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result <= n)]
pub fn prog(n: u32, c: bool) -> u32 {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    if c { i } else { 0 }
}
