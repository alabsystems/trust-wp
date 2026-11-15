//@ expect: reject
//@ mechanism: a three-arm `match k { 0 => m, 1 => 300, _ => 200 }` joins `m = id(y)`, which a later loop
//@ mechanism: writes `m = 150`; `r = id(w)` is returned under `ensures(result@ >= 100)`. The `k == 0` arm's
//@ mechanism: definition read `m` at the loop's exit.
//@ accept-means: a function that returns 5 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(5, 0)` returns 5.
//@ also-verified: id
//@ fixed-by: D-244 (a call result a later loop may change is named by a symbol of its site in a slice read
//@ fixed-by: after that loop, and every premise of the dependency closure, a join definition included, is
//@ fixed-by: retired where it reads a name a later loop may change)
//@ teeth: ACCEPTED at exit 0 with D-243; `failed` with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == y)]
pub fn id(y: u32) -> u32 { y }

#[ensures(result@ >= 100)]
pub fn go(y: u32, k: u8) -> u32 {
    let mut m = id(y);
    let w = match k { 0 => m, 1 => 300u32, _ => 200u32 };
    let r = id(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> m@ >= 100))]
    while i < 3 {
        m = 150;
        i += 1;
    }
    r
}
