//@ expect: reject
//@ mechanism: the `assert!` sibling of closure_index_through_option_map_uncharged. A contract-free
//@ mechanism: closure whose only panic site is an `assert!` arm is handed to `Option::map`, whose
//@ mechanism: builtin spec states the result and no precondition. The closure was a target of
//@ mechanism: nothing and the CONTRACTED host was credited.
//@ accept-means: `pick` is reported `verified` although `pick(Some(0))` panics with an assertion
//@ accept-means: failure inside the closure `Option::map` calls.
//@ fixed-by: D-118
//@ teeth: ACCEPTED (exit 0, `pick verified`) on the binary before D-118. After it the closure is a
//@ teeth: target, refuted on its assert, and `pick`'s credit is withdrawn.
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

// FALSE as a verified program function: `pick(Some(0))` fails the assert.
#[ensures(result@ == 1)]
pub fn pick(o: Option<u32>) -> u32 {
    let _ = o.map(|x| {
        assert!(x == 3);
        x
    });
    1
}
