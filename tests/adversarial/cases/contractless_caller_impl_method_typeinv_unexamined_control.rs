//@ expect: verify
//@ mechanism: the TRUE twin of contractless_caller_impl_method_typeinv_unexamined.rs: `hop` calls
//@ mechanism: `total` on a value that keeps its invariant, and the target it now is verifies.
//@ teeth: control — verified with discovery's grant arm on and off.
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
    Sum10 { a: 3, b: 7 }.total()
}
