//@ expect: reject
//@ mechanism: `let mut w = if c { atleast(y) } else { 200 }` writes the call's result straight into `w`,
//@ mechanism: `let r = atleast(w)`, and a later loop writes `w = 150`; `r` is returned under
//@ mechanism: `ensures(result@ >= 100)`. The arm's result was named by the bare destination `w`, so the
//@ mechanism: join definition `c ==> w$walk_join == w` read `w` at the loop's exit.
//@ accept-means: a function that returns 5 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(5, true)` returns 5.
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
pub fn go(y: u32, c: bool) -> u32 {
    let mut w = if c { atleast(y) } else { 200u32 };
    let r = atleast(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> w@ >= 100))]
    while i < 3 {
        w = 150;
        i += 1;
    }
    r
}
