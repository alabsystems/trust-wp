//@ expect: reject
//@ mechanism: `requires(c)` makes the join's call-result arm the only one: `let mut m = atleast(y); let w =
//@ mechanism: if c { m } else { 9 }; let r = atleast(w);`, a later loop writes `m = 9`, `ensures(result@ >
//@ mechanism: 5)`. The join definition read `m` at the loop's exit, where the invariant gives `m@ > 5`.
//@ accept-means: a function that returns 1 is credited with returning more than 5.
//@ WHY IT IS FALSE: `go(1, true)` returns 1.
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

#[requires(c)]
#[ensures(result@ > 5)]
pub fn go(y: u32, c: bool) -> u32 {
    let mut m = atleast(y);
    let w = if c { m } else { 9u32 };
    let r = atleast(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> m@ > 5))]
    while i < 3 {
        m = 9;
        i += 1;
    }
    r
}
