//@ expect: verify
//@ mechanism: otherwise arm made unreachable by a precondition that rules it out propositionally (no integer reasoning needed)
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x == 0u8 || x == 1u8)]
#[ensures(result@ >= 1)]
pub fn f(x: u8) -> u8 {
    match x {
        0 => 1,
        1 => 2,
        _ => unreachable!(),
    }
}
