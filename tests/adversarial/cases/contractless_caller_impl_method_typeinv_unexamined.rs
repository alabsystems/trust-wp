//@ expect: reject
//@ fn-failed: hop
//@ also-verified: <Sum10 as Total>::total
//@ mechanism: the direct-call spelling of contractless_caller_concrete_param_typeinv_unexamined.rs,
//@ mechanism: through a trait: a contract-free `hop` with no obligation of its own calls
//@ mechanism: `<Sum10 as Total>::total`, a local trait impl granted `inv(self)`, on a broken value. The
//@ mechanism: call resolves to that impl, whose grant makes `hop` a target
//@ mechanism: (`call_may_enter_invariant_grant`), so `hop` owes `inv(Sum10 { a: 1, b: 1 })` and is refuted.
//@ accept-means: a crate reported verified panics inside a trait impl it credits as panic-free.
//@ WHY THE PROGRAM IS WRONG: `hop()` calls `total` on a `Sum10` with `a + b == 2`, and `100 / (r - 2)`
//@ WHY THE PROGRAM IS WRONG: in `total` divides by zero.
//@ fixed-by: D-141 — a contract-free caller of a body granted a parameter invariant is a target.
//@ teeth: MEASURED on one build with discovery's grant arm knobbed off: ACCEPTED, exit 0, `total`
//@ teeth: verified; with it, `hop` FAILED.
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

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self) -> i32;
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        let r = self.a + self.b;
        100 / (r - 2) + 10 - 100 / (r - 2)
    }
}

pub fn hop() -> i32 {
    Sum10 { a: 1, b: 1 }.total()
}
