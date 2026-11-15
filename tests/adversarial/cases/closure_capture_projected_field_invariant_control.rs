//@ expect: verify
//@ mechanism: the TRUE twin of closure_capture_projected_field_invariant_free_grant, differing in
//@ mechanism: the captured field's VALUE alone. The obligation over a projected capture is
//@ mechanism: dischargeable exactly when the component the enclosing function wrote satisfies the
//@ mechanism: invariant, which is what says the reduction reads the right component rather than
//@ mechanism: refusing every projected capture.
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

pub struct Pair(pub u32, pub Zero);

#[ensures(result@ == 0)]
pub fn f() -> u32 {
    let p = Pair(3, Zero(0, 1));
    let clos = #[ensures(result@ == 0)]
    || { (*&p.1).0 };
    clos()
}
