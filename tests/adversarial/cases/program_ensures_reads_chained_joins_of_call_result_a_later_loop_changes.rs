//@ expect: reject
//@ mechanism: two joins chain: `w = if c { m } else { 200 }`, `v = if d { w } else { 300 }`, `r =
//@ mechanism: atleast(v)`, with `m = atleast(y)` written `m = 150` by a later loop; `ensures(result@ >=
//@ mechanism: 100)`. The definition of the second join pulls in the first, which read `m` at the loop's
//@ mechanism: exit.
//@ accept-means: a function that returns 5 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(5, true, true)` returns 5.
//@ also-verified: atleast
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

#[ensures(result@ >= 100)]
pub fn go(y: u32, c: bool, d: bool) -> u32 {
    let mut m = atleast(y);
    let w = if c { m } else { 200u32 };
    let v = if d { w } else { 300u32 };
    let r = atleast(v);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> m@ >= 100))]
    while i < 3 { m = 150; i += 1; }
    r
}
