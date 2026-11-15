//@ expect: reject
//@ mechanism: `let mut m = atleast(y); let w = if c { m } else { 200 }; let r = atleast(w);` before an
//@ mechanism: annotated loop that writes `m = 150`, and `r` is returned under `ensures(result@ >= 100)`.
//@ mechanism: The block-slice walker named `atleast`'s first result by the bare name `m`, which only the
//@ mechanism: later loop changes, and defined the join `c ==> w$walk_join == m`. In the function-level VC
//@ mechanism: the bare name `m` is its value at the loop's exit, where the invariant gives `m@ >= 100`;
//@ mechanism: D-243 (c) retired a callee postcondition that speaks of a name a later loop may change, but
//@ mechanism: the join definitions it pulls in (`PathBindings::definitions_read_by`) were stated unguarded
//@ mechanism: and never retired, so `r >= w$join == m >= 100` proved the claim.
//@ accept-means: a function that returns 5 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(5, true)` returns 5: the join reads `m` before the loop writes it.
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
    let mut m = atleast(y);
    let w = if c { m } else { 200u32 };
    let r = atleast(w);
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> m@ >= 100))]
    while i < 3 {
        m = 150;
        i += 1;
    }
    r
}
