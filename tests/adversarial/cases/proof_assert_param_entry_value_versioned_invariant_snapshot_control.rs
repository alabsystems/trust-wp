//@ expect: verify
//@ mechanism: control for the by-value parameter entry/current versioning (D-241): a parameter's type
//@ mechanism: invariant is an entry fact stated of its entry symbol, which a copy taken before the
//@ mechanism: re-bind and an unwritten field read; a `snapshot!` of a parameter freezes the value it
//@ mechanism: has when taken, the entry value or the value written before it.
//@ accept-means: n/a (control) — every claim here holds in every execution.
//@ fixed-by: n/a (control)
//@ teeth: on D-240 `snapshot_of_entry`'s `*s` claim and `snapshot_after_write` are FAILED; all verified
//@ teeth: with D-241.
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
pub fn invariant_of_copy(mut p: P) {
    let k = p.0;
    p = P(1, 1);
    proof_assert!(k@ > 0);
    let _ = p;
}

#[requires(true)]
pub fn invariant_of_unwritten_field(mut p: P) {
    p.1 = 9;
    proof_assert!(p.0@ > 0);
    let _ = p;
}

#[requires(x@ == 0)]
pub fn snapshot_of_entry(mut x: u32) {
    let s = snapshot!(x);
    x = 5;
    proof_assert!((*s)@ == 0);
    proof_assert!(x@ == 5);
}

#[requires(x@ == 0)]
pub fn snapshot_after_write(mut x: u32) {
    x = 5;
    let s = snapshot!(x);
    x = 6;
    proof_assert!((*s)@ == 5);
    let _ = x;
}
