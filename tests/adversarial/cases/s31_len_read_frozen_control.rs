//@ expect: verify
//@ mechanism: a length copy keeps its pre-call value (true: n is 0 after the push)
//@ fixed-by: s31 receiver copy freeze (closure.rs receiver_mutation_frozen_locals)
//@ accept-means: n/a (control)
//@ teeth: VERIFIED — FAILED on bc5554c (the copy was rebound to the post-push length), verifies with the s31 freeze.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn ctrl_len_zero_true() {
    let mut v: Vec<i32> = Vec::new();
    let n = v.len();
    v.push(1i32);
    proof_assert!(n@ == 0);
}
