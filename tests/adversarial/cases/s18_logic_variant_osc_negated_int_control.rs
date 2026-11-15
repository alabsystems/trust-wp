//@ expect: verify
//@ mechanism: Int-variant decrease goal proves `0 <= variant` — control (nonnegativity is the fn's own requires)
//@ fixed-by: s18 (variant.rs prove_self_variant_decrease: `before >= 0` is a goal only)
//@ accept-means: n/a (control) — a requires-guarded decreasing Int variant must stay accepted
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
#[requires(x >= 0)]
#[variant(x)]
pub fn down(x: Int) -> Int {
    if x > 0 { down(x - 1) } else { 0 }
}

pub fn uses_down() {
    proof_assert! { down(0) == 0 };
}
