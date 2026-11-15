//@ expect: verify
//@ mechanism: control for D-143's opaque-binding rule: two shadowed locals bound to TRANSLATED values
//@ mechanism: (an integer widening) have exact expressions, not a shared symbol, so the second panic
//@ mechanism: arm's charge is proved from the first check and the edge is dead.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn f(p: u32) {
    let a = p as u64;
    if a == 5 {
        return;
    }
    let a = p as u64;
    if a == 5 {
        panic!()
    }
}
