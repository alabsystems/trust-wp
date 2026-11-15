//@ expect: verify
//@ mechanism: the TRUE twin of trait_default_body_override_typeinv_free_grant: the same trait,
//@ mechanism: the same overriding impl, the same claim, and a receiver that SATISFIES the
//@ mechanism: invariant because the caller forwards its own parameter untouched. It is what
//@ mechanism: says whether a fix for the reject twin charges the obligation or just refuses
//@ mechanism: every receiver. It verifies today only because no obligation is charged at all;
//@ mechanism: after the grant is charged it must verify by DISCHARGING it from `caller`'s own
//@ mechanism: parameter invariant.
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
pub fn caller(s: Sum10) -> i32 {
    s.total()
}
