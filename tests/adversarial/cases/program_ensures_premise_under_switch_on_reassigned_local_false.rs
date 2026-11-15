//@ expect: reject
//@ mechanism: `let mut lim = 200; lim = x; if lim > 100 { r = big() }` before an annotated loop, `r`
//@ mechanism: returned under `ensures(result@ >= 100)`. D-244 reads a switch on a local the path walk
//@ mechanism: follows at its value at the switch: `x > 100`, never the earlier `200`.
//@ accept-means: a function that returns 0 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(0)` returns 0.
//@ also-verified: big
//@ teeth: rejected with D-243 and with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ >= 100)]
pub fn big() -> u32 { 100 }

#[ensures(result@ >= 100)]
pub fn go(x: u32) -> u32 {
    let mut lim = 200u32;
    lim = x;
    let mut r = 0u32;
    if lim > 100 { r = big(); }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    r
}
