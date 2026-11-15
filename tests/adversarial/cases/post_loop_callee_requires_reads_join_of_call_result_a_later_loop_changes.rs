//@ expect: reject
//@ mechanism: the join of `m = atleast(y)` is read by `r = atleast(w)` before an annotated loop that writes
//@ mechanism: `m = 150`, and `need100(r)` (`requires(k@ >= 100)`) is called after the loop. The join
//@ mechanism: definition read `m` at the loop's exit and discharged the precondition.
//@ accept-means: a callee's precondition is discharged for a call that passes 5.
//@ WHY IT IS FALSE: `go(5, true)` calls `need100(5)`.
//@ also-verified: small, medium, atleast, need100
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

#[requires(k@ >= 100)]
pub fn need100(k: u32) {}

pub fn go(y: u32, c: bool) {
    let mut m = atleast(y);
    let w = if c { m } else { 200u32 };
    let r = atleast(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> m@ >= 100))]
    while i < 3 {
        m = 150;
        i += 1;
    }
    need100(r);
}
