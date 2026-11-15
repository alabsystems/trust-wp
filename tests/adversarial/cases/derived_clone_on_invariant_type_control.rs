//@ expect: verify
//@ xfail: D-141's price in its most common spelling: a `#[derive(Clone)]` is an impl of a foreign
//@ xfail: trait's method, so its body holds no `inv(*self)` premise and its `inv(result)` goal is
//@ xfail: refuted (std's `Vec::clone` can hand it a `Sum10` with `a + b == 2`). Creusot charges
//@ xfail: `inv` at every call into std and verifies it.
//@ xfail-verdict: failed
//@ mechanism: a derived `Clone` on a type with an invariant, nothing else: the copy of a value that
//@ mechanism: keeps its invariant keeps it.
//@ teeth: control — `<Sum10 as Clone>::clone` verified with the foreign-impl arm knobbed off, and
//@ teeth: `FAILED` with it on; `make` verified both ways.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone)]
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

#[ensures(result.a@ + result.b@ == 10)]
pub fn make() -> Sum10 {
    Sum10 { a: 3, b: 7 }
}
