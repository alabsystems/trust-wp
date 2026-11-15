//@ expect: reject
//@ mechanism: the join of `m = atleast(y)` is read by `r = atleast(w)` before two annotated loops, and only
//@ mechanism: the second one writes `m = 150`; `r` is returned under `ensures(result@ >= 100)`. The join
//@ mechanism: definition read `m` at the second loop's exit.
//@ accept-means: a function that returns 5 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(5, true)` returns 5.
//@ also-verified: small, medium, atleast
//@ fixed-by: D-244 (a call result a later loop may change is named by a symbol of its site in a slice read
//@ fixed-by: after that loop, and every premise of the dependency closure, a join definition included, is
//@ fixed-by: retired where it reads a name a later loop may change)
//@ teeth: ACCEPTED at exit 0 with D-243; `failed` with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 10)]
pub fn small() -> u32 { 3 }

#[ensures(result@ < 20)]
pub fn medium() -> u32 { 15 }

#[ensures(result@ >= y@)]
pub fn atleast(y: u32) -> u32 { y }

#[ensures(result@ >= 100)]
pub fn go(y: u32, c: bool) -> u32 {
    let mut m = atleast(y);
    let w = if c { m } else { 200u32 };
    let r = atleast(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    let mut j = 0u32;
    #[invariant(j@ <= 3 && (j@ > 0 ==> m@ >= 100))]
    while j < 3 {
        m = 150;
        j += 1;
    }
    r
}
