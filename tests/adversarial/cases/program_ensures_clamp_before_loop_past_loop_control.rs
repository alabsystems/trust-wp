//@ expect: verify
//@ mechanism: `let mut lim = x; if lim > 100 { lim = 100 }` before an annotated loop, `lim` returned under
//@ mechanism: `ensures(result@ <= 100)`. The switch reads `lim`, which one arm then reassigns: D-243
//@ mechanism: refused it by the flat walker's strict stability rule, so the join was undefined. The path
//@ mechanism: walk's binding at the switch is `x`; D-244 refuses only writes the walk does not see and a
//@ mechanism: reassigned parameter (`switch_discr_is_path_stable`). Verified before D-243; `failed` with
//@ mechanism: D-243 (an over-refusal); verifies with D-244.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 1000)]
pub fn compute() -> u32 { 7 }

#[ensures(result@ <= 100)]
pub fn go(x: u32, n: u32) -> u32 {
    let mut lim = x;
    if lim > 100 { lim = 100; }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    lim
}
