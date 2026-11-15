//@ expect: verify
//@ mechanism: drop glue — over-refusal control
//@ fixed-by: s44 (wp-s44, contracted panic sites)
//@ accept-means: n/a (control) — the Drop impl is contracted (requires true) and verified as its own item.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

struct D;

impl Drop for D {
    #[requires(true)]
    #[ensures(true)]
    fn drop(&mut self) {}
}

#[ensures(result@ == x@)]
pub fn drop_ok(x: u8) -> u8 {
    let _d = D;
    x
}
