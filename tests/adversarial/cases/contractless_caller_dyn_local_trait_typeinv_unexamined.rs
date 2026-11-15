//@ expect: reject
//@ also-verified: <Sum10 as Tr>::m
//@ mechanism: a contract-free `hop` calls a LOCAL trait's method through `dyn Tr`. The impl
//@ mechanism: `<Sum10 as Tr>::m` holds `inv(*self)`: every route into a local trait's impl is a call a
//@ mechanism: lane walks. The call does not determine which body it enters, so discovery reads the
//@ mechanism: declaration and every local implementation (`call_may_enter_invariant_grant`), finds the
//@ mechanism: impl's grant, and makes `hop` a target; its call lane cannot state the grant through a
//@ mechanism: `dyn` call and refuses it. With `hop` examined by nothing, `m` was credited on a premise
//@ mechanism: nobody paid for and the crate exited 0.
//@ accept-means: a crate reported verified panics inside a trait impl it credits as panic-free.
//@ WHY THE PROGRAM IS WRONG: `hop()` boxes a `Sum10` with `a + b == 2` as `dyn Tr`, and `100 / (r - 2)` in `m`
//@ WHY THE PROGRAM IS WRONG: divides by zero.
//@ fixed-by: D-141 — a contract-free caller of a body granted a parameter invariant is a target.
//@ teeth: MEASURED on one build with the three route arms knobbed off: ACCEPTED, exit 0, `m`
//@ teeth: verified; with them, `hop` unknown.
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

pub trait Tr {
    fn m(&self) -> i32;
}

impl Tr for Sum10 {
    fn m(&self) -> i32 {
        let r = self.a + self.b;
        100 / (r - 2)
    }
}

pub fn hop() -> i32 {
    let b: Box<dyn Tr> = Box::new(Sum10 { a: 1, b: 1 });
    b.m()
}
