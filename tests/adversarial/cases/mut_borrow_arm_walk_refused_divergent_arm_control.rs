//@ expect: verify
//@ timeout: 300
//@ mechanism: the mut-borrow lane merges a boolean switch's arms as `Ite(cond, then, else)`, and drops an
//@ mechanism: arm whose walk returns `None` only when every path of it diverges (`block_must_diverge`).
//@ mechanism: control: the else arm's `match x` is a non-boolean switch the walk cannot follow, but both of
//@ mechanism: its arms panic, so the final value is the then arm's on every returning execution. Twin of
//@ mechanism: mut_borrow_arm_walk_refused_is_not_divergence.rs. The solver needs more than the default budget
//@ mechanism: under load, hence the long one.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(flag)]
#[ensures((^a)[0]@ == 3)]
pub fn g(a: &mut [u32; 2], flag: bool, x: u32) {
    if flag {
        a[0] = 3;
    } else {
        match x {
            1 => panic!(),
            _ => unreachable!(),
        }
    }
}
