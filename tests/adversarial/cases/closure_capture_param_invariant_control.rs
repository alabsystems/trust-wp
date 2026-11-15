//@ expect: verify
//@ mechanism: the construction-site obligation over a capture the enclosing function did NOT
//@ mechanism: build: `x` is its own parameter, so it already holds `inv(x)` as a premise and the
//@ mechanism: obligation discharges by matching it (D-63's route), with no unfolding involved.
//@ mechanism: Pins the floor of the closure-capture obligation: a fix that refused every capture
//@ mechanism: would break this without breaking the value-differing twins beside it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::*, prelude::*};

pub struct Zero(pub u32, pub u32);

impl Invariant for Zero {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ == 0 }
    }
}

#[ensures(result@ == 0)]
pub fn g(x: Zero) -> u32 {
    let clos = #[ensures(result@ == 0)]
    || { (*&x).0 };
    clos()
}
