//@ expect: reject
//@ mechanism: the false sibling of program_ensures_else_if_clamp_before_loop_control.rs: `if lim > 100 {
//@ mechanism: lim = 100 } else if lim > 50 { lim = 50 }` returned past an annotated loop under
//@ mechanism: `ensures(result@ <= 50)`; the first arm leaves 100.
//@ accept-means: a function that returns 100 is credited with returning at most 50.
//@ WHY IT IS FALSE: `go(200)` returns 100.
//@ teeth: rejected with D-243 and with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ <= 50)]
pub fn go(x: u32) -> u32 {
    let mut lim = x;
    if lim > 100 { lim = 100; } else if lim > 50 { lim = 50; }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    lim
}
