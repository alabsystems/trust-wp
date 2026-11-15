//@ expect: verify
//@ mechanism: control: a contract that reads a struct field's final value through `&mut` twice,
//@ mechanism: here in two postconditions over `Int` views. One read verifies (the s34 controls);
//@ mechanism: two do not, so any clause that repeats such a read (D-232's case split of a wrapping
//@ mechanism: operator does) pays this price.
//@ WHY THE CONTRACT IS TRUE: n.a < 100 before the body adds 1 to it, so the final field is n.a + 1,
//@ WHY THE CONTRACT IS TRUE: which is at least 1.
//@ xfail: ay times out on the goal once the field's final value is read twice; it was so before
//@ xfail: D-232.
//@ xfail-verdict: unknown
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct N {
    pub a: u32,
}

#[requires(n.a < 100u32)]
#[ensures((^n).a@ == n.a@ + 1)]
#[ensures((^n).a@ >= 1)]
pub fn mut_n(n: &mut N) {
    n.a += 1;
}
