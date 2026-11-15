//@ expect: reject
//@ mechanism: the closure handed to `Option::map` holds no assert, abort or bounds check of its own:
//@ mechanism: it CALLS another closure, `f`, whose body indexes. The call is `Fn::call`, whose
//@ mechanism: builtin spec requires `f`'s precondition, which D-54 reads as `f`'s body WP, so the
//@ mechanism: escaping closure owes `f`'s bounds check through its callee-precondition arm. In
//@ mechanism: `pick_inner`, `f` is defined INSIDE the escaping closure and escapes nowhere; in
//@ mechanism: `pick`, `f` is the host's and rides in the escaping closure's capture.
//@ accept-means: a host is reported `verified` although calling it with `Some(0)` and an empty slice
//@ accept-means: indexes past the end in `f`, called by the closure `Option::map` runs.
//@ WHY THE CONTRACT IS FALSE: `pick(Some(0), &[])` and `pick_inner(Some(0), &[])` panic with
//@ WHY THE CONTRACT IS FALSE: "index out of bounds".
//@ fixed-by: D-118: the escaping closure is a target and each host rests on its verdict.
//@ teeth: ACCEPTED, exit 0, both hosts `verified`, on the binary before D-118. After it each
//@ teeth: escaping closure is refuted on `f`'s precondition and each host's credit is withdrawn.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// FALSE: `pick(Some(0), &[])` indexes an empty slice.
#[ensures(result@ == 1)]
pub fn pick(o: Option<usize>, w: &[u32]) -> u32 {
    let f = |j: usize| w[j];
    let _ = o.map(|j| f(j));
    1
}

// FALSE: `pick_inner(Some(0), &[])` indexes an empty slice.
#[ensures(result@ == 1)]
pub fn pick_inner(o: Option<usize>, w: &[u32]) -> u32 {
    let _ = o.map(|j| {
        let f = |k: usize| w[k];
        f(j)
    });
    1
}
