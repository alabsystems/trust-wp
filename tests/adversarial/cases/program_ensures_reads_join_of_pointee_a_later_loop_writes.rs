//@ expect: reject
//@ mechanism: `let w = if c { *p } else { 200 }` over `p: &mut u32`, `let r = atleast(w)`, and a later loop
//@ mechanism: stores `*p = 150`; `r` is returned under `ensures(result@ >= 100)`. The join definition `c
//@ mechanism: ==> w$walk_join == *p` read the pointee at the loop's exit. No call result is involved: the
//@ mechanism: definition reads a name through a pointer a later loop writes through.
//@ accept-means: a function that returns 5 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(&mut 5, true)` returns 5.
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
pub fn go(p: &mut u32, c: bool) -> u32 {
    let w = if c { *p } else { 200u32 };
    let r = atleast(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> (*p)@ >= 100))]
    while i < 3 {
        *p = 150;
        i += 1;
    }
    r
}
