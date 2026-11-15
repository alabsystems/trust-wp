//@ expect: verify
//@ mechanism: a three-arm `match` before an annotated loop: the join symbol of `m` is defined by each arm's
//@ mechanism: condition (`k == 0`, `k == 1`, and the `otherwise` conjunction), and every arm's value satisfies
//@ mechanism: `need_ge5`. A control for D-243's join definitions.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k >= 5u32)]
pub fn need_ge5(k: u32) {}

pub fn f(k: u32) {
    let m = match k {
        0 => 5u32,
        1 => 6u32,
        _ => 7u32,
    };
    need_ge5(m);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
}
