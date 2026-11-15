//@ expect: verify
//@ mechanism: the isolating twin of callee_typeinv_free_grant_generic_marker: the same
//@ mechanism: marker-minting contract and the same caller-built argument, differing only in
//@ mechanism: whether the invariant is satisfied. See
//@ mechanism: callee_typeinv_ctor_arg_trait_method_control for why the free-grant case's own
//@ mechanism: control cannot supply this.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Meas {
    #[logic]
    fn meas(self) -> Int;
}

pub struct Unit;

impl Meas for Unit {
    #[logic(open)]
    fn meas(self) -> Int {
        pearlite! { 0 }
    }
}

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
#[ensures(t.meas() == t.meas())]
pub fn total<T: Meas>(t: T, s: Sum10) -> i32 {
    s.a + s.b
}

#[ensures(result@ == 10)]
pub fn caller() -> i32 {
    total(Unit, Sum10 { a: 4, b: 6 })
}
