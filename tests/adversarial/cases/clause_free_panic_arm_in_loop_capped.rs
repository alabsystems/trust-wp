//@ expect: verify
//@ xfail: D-142 reads proved-dead edges only from the primary walk of a loop-free body with exact
//@ xfail: values; in a body with a loop the primary walk's in-loop obligations are filtered out and
//@ xfail: restated by region walks that record nothing, so the cap still counts this panic call.
//@ mechanism: price of D-142 — a clause-free loop whose panic arm is provably dead.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop(n: u32) {
    let mut i = 0u32;
    while i < n {
        if i > n {
            panic!("never");
        }
        i += 1;
    }
}
