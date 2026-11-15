//@ expect: reject
//@ mechanism: a join of two call results, `w = if c { m } else { n }` with `m = id(y)` and `n = id(z)`; a
//@ mechanism: later loop writes `m = 150`, and `if c { r } else { 100 }` is returned under `ensures(result@
//@ mechanism: >= 100)` with `r = atleast(w)`. Found probing sideways of the D-243 verifier's reports.
//@ accept-means: a function that returns 5 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(5, 0, true)` returns 5.
//@ also-verified: atleast, id
//@ fixed-by: D-244 (a call result a later loop may change is named by a symbol of its site in a slice read
//@ fixed-by: after that loop, and every premise of the dependency closure, a join definition included, is
//@ fixed-by: retired where it reads a name a later loop may change)
//@ teeth: ACCEPTED at exit 0 with D-243; `failed` with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ >= y@)]
pub fn atleast(y: u32) -> u32 { y }

#[ensures(result == y)]
pub fn id(y: u32) -> u32 { y }

#[ensures(result@ >= 100)]
pub fn go(y: u32, z: u32, c: bool) -> u32 {
    let mut m = id(y);
    let n = id(z);
    let w = if c { m } else { n };
    let r = atleast(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> m@ >= 100))]
    while i < 3 { m = 150; i += 1; }
    if c { r } else { 100 }
}
