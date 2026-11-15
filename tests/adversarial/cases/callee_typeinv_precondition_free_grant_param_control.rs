//@ expect: verify
//@ mechanism: the free-function family's non-xfail control. Its two committed controls both
//@ mechanism: pass an inline struct literal, whose translation loses the parameter's ADT
//@ mechanism: sort, so both are over-refused and neither can tell a working obligation from a
//@ mechanism: blanket refusal. Here the caller forwards its OWN parameter, so the obligation
//@ mechanism: is discharged by the premise the caller already holds — and a regression that
//@ mechanism: refuses every argument shows up here as a break.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for Sum10 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

#[ensures(result@ == 10)]
pub fn total(s: Sum10) -> i32 {
    s.a + s.b
}

#[ensures(result@ == 10)]
pub fn caller(s: Sum10) -> i32 {
    total(s)
}
