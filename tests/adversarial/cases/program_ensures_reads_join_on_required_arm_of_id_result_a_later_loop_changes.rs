//@ expect: reject
//@ mechanism: `requires(c)` selects the call-result arm of `w = if c { m } else { 7 }`, `m = id(y)` is
//@ mechanism: written `m = 7` by a later loop, `r = id(w)` is returned under `ensures(result == 7u32)`. The
//@ mechanism: join definition read `m` at the loop's exit. On D-243 ay answered UNSAT for this false
//@ mechanism: contract and only the certificate gate withheld the proof (`unknown`, proof-trusted); `ay-
//@ mechanism: not-unsat` pins the rejection to the VC itself.
//@ accept-means: a function that returns 3 is credited with returning 7.
//@ WHY IT IS FALSE: `go(3, true)` returns 3.
//@ also-verified: id
//@ ay-not-unsat: go
//@ fixed-by: D-244 (a call result a later loop may change is named by a symbol of its site in a slice read
//@ fixed-by: after that loop, and every premise of the dependency closure, a join definition included, is
//@ fixed-by: retired where it reads a name a later loop may change)
//@ teeth: `unknown` with ay UNSAT on D-243; `failed`, ay SAT, with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == y)]
pub fn id(y: u32) -> u32 { y }

#[requires(c)]
#[ensures(result == 7u32)]
pub fn go(y: u32, c: bool) -> u32 {
    let mut m = id(y);
    let w = if c { m } else { 7u32 };
    let r = id(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> m == 7u32))]
    while i < 3 {
        m = 7;
        i += 1;
    }
    r
}
