//@ expect: verify
//@ mechanism: the TRUE twin of closure_fnmut_breaks_capture_invariant_verified, identical but for
//@ mechanism: the value written, which keeps `Small`'s invariant. A fix that owes `inv` of each
//@ mechanism: mutably captured value at the closure's exit must still verify this.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓`, `f::{closure#2} verified ✓`, the same verdicts as its RED
//@ teeth: twin.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::*, prelude::*};

pub struct Small(pub u8);

impl Invariant for Small {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ < 3 }
    }
}

#[ensures(true)]
pub fn f() {
    let mut s = Small(0);
    let mut c = #[ensures(true)]
    || {
        let r = &mut s;
        r.0 = 1;
    };
    c();
}
