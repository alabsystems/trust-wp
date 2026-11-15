//@ expect: verify
//@ mechanism: the isolating twin of trait_default_body_override_typeinv_generic_hop: the same
//@ mechanism: overwrite of `s` before the same hop into the same overriding impl, differing
//@ mechanism: only in the values written — 4 and 6, which keep `Sum10`'s invariant. The pair
//@ mechanism: separates the instantiating call's obligation from a refusal of the hop (D-68,
//@ mechanism: D-141).
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

pub trait Total: Sized {
    #[ensures(result@ == 10)]
    fn total(self) -> i32 {
        10
    }
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T) -> i32 {
    t.total()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 4;
    s.b = 6;
    via(s)
}
