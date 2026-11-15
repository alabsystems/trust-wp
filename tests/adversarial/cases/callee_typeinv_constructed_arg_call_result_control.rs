//@ expect: verify
//@ mechanism: the far side of the over-refusal boundary recorded by
//@ mechanism: callee_typeinv_constructed_arg_tautological_control. The argument is a CALL
//@ mechanism: RESULT, and a callee whose return type carries an invariant gets that
//@ mechanism: invariant as a synthesized postcondition — so the caller HOLDS `inv(arg)` and
//@ mechanism: the obligation is discharged by the premise, never by unfolding the body.
//@ mechanism: A regression here would mean the obligation stopped being dischargeable by
//@ mechanism: the one route that works.
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

#[ensures(result.a@ == 4)]
#[ensures(result.b@ == 6)]
pub fn mk() -> Sum10 {
    Sum10 { a: 4, b: 6 }
}

#[ensures(result@ == 10)]
pub fn total(s: Sum10) -> i32 {
    s.a + s.b
}

#[ensures(result@ == 10)]
pub fn caller() -> i32 {
    total(mk())
}
