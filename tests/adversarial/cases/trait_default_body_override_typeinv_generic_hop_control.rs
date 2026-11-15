//@ expect: verify
//@ mechanism: the TRUE twin of trait_default_body_override_typeinv_generic_hop — the same hop
//@ mechanism: into the same overriding impl, with a receiver whose invariant the caller holds
//@ mechanism: as its own parameter. The declaration's `Self` clause stated at `Sum10` covers
//@ mechanism: the override, so the hop charges instead of refusing (D-141).
//@ mechanism: `..._value_control` is the twin differing in the value alone.
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
pub fn caller(s: Sum10) -> i32 {
    via(s)
}
