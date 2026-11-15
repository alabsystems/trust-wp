//@ expect: reject
//@ mechanism: the primitive integer DIV spec (result@ == self@ / rhs@) was listed under the bare
//@ mechanism: trait path core::ops::Div::div, which the trait-method fallback looks up for EVERY
//@ mechanism: Div impl - a user type inherited integer division semantics.
//@ fixed-by: wp-s43 integer Div/Rem spec commit (integer-typed aliases only)
//@ accept-means: a user operator impl is again given a primitive integer spec.
//@ WHY THE CONTRACTS ARE FALSE: S::div returns S(0) and S::rem returns S(5).
//@ teeth: user_div_false and user_div_op_false verified before the fix, measured on a
//@ teeth: probe program with a user `Div` impl on an i32 newtype.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::ops::{Div, Rem};

pub struct S(pub i32);

impl View for S {
    type ViewTy = Int;
    #[logic(open)]
    fn view(self) -> Int {
        pearlite! { self.0@ }
    }
}

impl Div for S {
    type Output = S;
    fn div(self, _r: S) -> S {
        S(0)
    }
}

impl Rem for S {
    type Output = S;
    fn rem(self, _r: S) -> S {
        S(5)
    }
}

pub fn user_div_false() {
    let r = S(8).div(S(2));
    proof_assert!(r@ == 4);
}

pub fn user_div_op_false() {
    let r = S(8) / S(2);
    proof_assert!(r@ == 4);
}

pub fn user_rem_false() {
    let r = S(8).rem(S(3));
    proof_assert!(r@ == 2);
}
