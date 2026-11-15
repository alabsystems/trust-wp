//@ expect: verify
//@ mechanism: control for proof_assert_param_type_invariant_read_after_rebind: the entry invariant of a
//@ mechanism: by-value parameter read before any write, and the same assertion after a re-bind or a field
//@ mechanism: write of a value that satisfies it (`p = P(3, 1)`, `p.0 = 3`), each TRUE. Withdrawing the
//@ mechanism: entry invariant of a re-bound parameter must keep all three.
//@ accept-means: n/a (control)
//@ fixed-by: n/a (control)
//@ teeth: n/a — over-refusal control; verified on D-140's driver and on the campaign driver.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::*, prelude::*};

pub struct P(pub u32, pub u32);

impl Invariant for P {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ > 0 }
    }
}

#[requires(true)]
pub fn at_entry(p: P) {
    proof_assert!(p.0@ > 0);
    let _ = p;
}

#[requires(true)]
pub fn rebind_known(mut p: P) {
    p = P(3, 1);
    proof_assert!(p.0@ > 0);
    let _ = p;
}

#[requires(true)]
pub fn field_write_known(mut p: P) {
    p.0 = 3;
    proof_assert!(p.0@ > 0);
    let _ = p;
}
