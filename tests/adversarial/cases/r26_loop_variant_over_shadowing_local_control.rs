//@ expect: verify
//@ mechanism: control for D-238's loop variant resolution: a variant names the binding visible at
//@ mechanism: its loop, here the local that shadows the parameter `n`. Read by its source name it
//@ mechanism: was the parameter, which the loop never changes, so the decrease failed.
//@ accept-means: n/a (control) - the shadowing local decreases on every iteration.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
pub fn ov1(n: u32) {
    let mut n = n;
    #[invariant(true)]
    #[variant(n)]
    while n > 0 {
        n -= 1;
    }
}
