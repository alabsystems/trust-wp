//@ expect: verify
//@ mechanism: a length copy relates to the post-call length (true: n@ + 1 == v@.len())
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: n/a (control)
//@ xfail: Vec::push post-state length is not related to the frozen pre-call read (p3 ctrl_len_push_true)
//@ teeth: UNVERIFIED — FAILED on bc5554c and with the s31 freeze (incomplete Vec::push post-state reasoning here).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn ctrl_len_push_true() {
    let mut v: Vec<i32> = Vec::new();
    let n = v.len();
    v.push(1i32);
    proof_assert!(n@ + 1 == v@.len());
}
