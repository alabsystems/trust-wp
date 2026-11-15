//@ expect: verify
//@ mechanism: control: a call on ONE arm of a branch inside the loop body. Its postcondition
//@ mechanism: speaks for the path that makes the call, under that path's condition, and the other
//@ mechanism: arm keeps its own value; `x != 7u32` is TRUE and inductive.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result < 7u32)]
pub fn below() -> u32 { 0 }

pub fn go(n: u32) {
    let mut i: u32 = 0;
    let mut x: u32 = 5;
    #[invariant(x != 7u32)]
    while i < n {
        if i == 0u32 { x = 6; } else { x = below(); }
        i += 1;
    }
}
