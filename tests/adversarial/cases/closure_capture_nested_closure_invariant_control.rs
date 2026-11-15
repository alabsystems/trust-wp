//@ expect: verify
//@ mechanism: the TRUE twin of closure_capture_nested_closure_invariant_free_grant, differing in
//@ mechanism: the captured value alone. The inner closure's construction obligation is owed
//@ mechanism: inside the OUTER closure's body and discharges against the premise that body
//@ mechanism: already holds about the same environment slot; a spelling mismatch between the two
//@ mechanism: would refuse this without refusing the false twin any harder.
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
    let outer = #[ensures(result@ == 0)]
    || {
        let inner = #[ensures(result@ == 0)]
        || { (*&x).0 };
        inner()
    };
    outer()
}
