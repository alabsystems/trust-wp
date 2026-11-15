//@ expect: reject
//@ mechanism: `b = big(w)` (`ensures(result == (k@ >= 100))`) over the join of `m = atleast(y)`, which a
//@ mechanism: later loop writes `m = 150`; `b` is returned under `ensures(result)`. The join definition
//@ mechanism: read `m` at the loop's exit and made `big`'s postcondition say `true`.
//@ accept-means: a function that returns `false` is credited with returning `true`.
//@ WHY IT IS FALSE: `go(5, true)` returns `false`.
//@ also-verified: atleast, big
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

#[ensures(result == (k@ >= 100))]
pub fn big(k: u32) -> bool { k >= 100 }

#[ensures(result)]
pub fn go(y: u32, c: bool) -> bool {
    let mut m = atleast(y);
    let w = if c { m } else { 200u32 };
    let b = big(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> m@ >= 100))]
    while i < 3 { m = 150; i += 1; }
    b
}
