//@ expect: reject
//@ mechanism: `w = if c { y } else { 200 }` reads the parameter `y`, which a later loop writes `y = 150`;
//@ mechanism: `r = atleast(w)` is returned under `ensures(result@ >= 100)`. A scope guard of D-244's
//@ mechanism: retirement of a join definition that reads a parameter a later loop changes; the loop's call
//@ mechanism: obligations also fail closed on the written parameter.
//@ accept-means: a function that returns 5 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(5, true)` returns 5.
//@ also-verified: atleast
//@ teeth: `unknown` with D-243 and with D-244 (the loop's own lane fails closed); the function-level slice
//@ teeth: states no definition reading `y` with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ >= y@)]
pub fn atleast(y: u32) -> u32 { y }

#[ensures(result@ >= 100)]
pub fn go(mut y: u32, c: bool) -> u32 {
    let w = if c { y } else { 200u32 };
    let r = atleast(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> y@ >= 100))]
    while i < 3 { y = 150; i += 1; }
    r
}
