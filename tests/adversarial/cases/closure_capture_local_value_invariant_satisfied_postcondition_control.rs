//@ expect: verify
//@ mechanism: the TRUE twin of closure_capture_local_value_invariant_free_grant, differing in
//@ mechanism: the CAPTURED VALUE alone: `Zero(0, 1)` satisfies the invariant the closure's body
//@ mechanism: is granted, `Zero(7, 1)` does not. Its job is D-68's: the construction-site
//@ mechanism: obligation is real only if a pair isolates it, and a control that discharged by
//@ mechanism: some other route — a parameter the enclosing function already holds `inv` of —
//@ mechanism: could not tell the obligation from a blanket refusal of built aggregates.
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
pub fn f() -> u32 {
    let x = Zero(0, 1);
    let clos = #[ensures(result@ == 0)]
    || { (*&x).0 };
    clos()
}
