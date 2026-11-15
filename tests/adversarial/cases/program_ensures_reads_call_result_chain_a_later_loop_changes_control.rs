//@ expect: verify
//@ mechanism: `let mut m = atleast(y); let r = atleast(m)` before an annotated loop that writes `m = 150`,
//@ mechanism: `r` returned under `ensures(result@ >= y@)`. D-243 retired `r`'s premise, which read `m`;
//@ mechanism: D-244 names `m`'s result by its site in the function-level slice, so both premises read one
//@ mechanism: value. `failed` with D-243; verifies with D-244.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ >= y@)]
pub fn atleast(y: u32) -> u32 { y }

#[ensures(result@ >= y@)]
pub fn go(y: u32) -> u32 {
    let mut m = atleast(y);
    let r = atleast(m);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { m = 150; i += 1; }
    r
}
