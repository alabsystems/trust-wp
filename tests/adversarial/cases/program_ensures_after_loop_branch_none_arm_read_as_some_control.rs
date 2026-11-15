//@ expect: verify
//@ mechanism: control for program_ensures_after_loop_branch_none_arm_read_as_some: the arm the branch takes when `c` holds is `None`. FAILED with a counterexample at the campaign tip, where the post-loop walk read the branch as its `Some(i)` arm alone.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(c ==> result == None)]
pub fn prog(n: u32, c: bool) -> Option<u32> {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    if c { None } else { Some(i) }
}
