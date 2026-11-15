//@ expect: reject
//@ mechanism: the false sibling of program_ensures_clamp_before_loop_past_loop_control.rs: `let mut lim =
//@ mechanism: x; if lim > 100 { lim = 100 }` before an annotated loop, `lim` returned under
//@ mechanism: `ensures(result@ <= 99)`. D-244 reads a switch on a local one arm reassigns at the local's
//@ mechanism: value at the switch; the join is then `lim > 100 ==> lim == 100`, `!(lim > 100) ==> lim ==
//@ mechanism: x`, which allows 100.
//@ accept-means: a function that returns 100 is credited with returning at most 99.
//@ WHY IT IS FALSE: `go(100)` returns 100.
//@ teeth: rejected with D-243 and with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ <= 99)]
pub fn go(x: u32) -> u32 {
    let mut lim = x;
    if lim > 100 { lim = 100; }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    lim
}
