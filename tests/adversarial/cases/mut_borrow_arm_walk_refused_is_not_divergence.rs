//@ expect: reject
//@ mechanism: the mut-borrow lane merges a boolean switch's arms as `Ite(cond, then, else)`, and an arm
//@ mechanism: whose walk returns `None` was taken to diverge: the other arm's state became the final
//@ mechanism: value on every path. `None` is also what the walk returns for an arm it cannot follow (here
//@ mechanism: the non-boolean `match x`), which returns. So `^a == (*a)@.set(0, 3)` was bound
//@ mechanism: unconditionally, and the indexed-write facts read off it with it. `process_switch_int` now
//@ mechanism: drops only an arm every path of which diverges (`block_must_diverge`), and refuses otherwise.
//@ accept-means: a function that writes `a[0]` only when `flag` holds is verified against a final value
//@ accept-means: that holds 3 there on every path, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `g(&mut [0, 0], false, 1)` leaves `a[0] == 0`.
//@ teeth: ACCEPTED before D-169 (the lane's final value, traced: `(*a)@.set(0, 3)`, no
//@ teeth: `Ite`); rejected with D-169.
//@ fixed-by: D-169 (an arm the mut-borrow walk cannot follow is not an arm no execution returns through).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures((^a)[0]@ == 3)]
pub fn g(a: &mut [u32; 2], flag: bool, x: u32) {
    if flag {
        a[0] = 3;
    } else {
        match x {
            1 => a[1] = 5,
            7 => a[1] = 6,
            _ => {}
        }
    }
}
