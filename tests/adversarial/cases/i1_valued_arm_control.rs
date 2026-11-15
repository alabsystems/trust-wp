//@ expect: verify
//@ mechanism: a valued panic arm made unreachable by the precondition, wildcard arm survives
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ != 0)]
#[ensures(result@ == x@)]
pub fn f(x: u8) -> u8 {
    match x {
        0 => panic!(),
        _ => x,
    }
}
