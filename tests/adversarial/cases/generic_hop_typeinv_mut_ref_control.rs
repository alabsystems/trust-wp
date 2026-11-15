//@ expect: verify
//@ timeout: 300
//@ mechanism: the TRUE twin of generic_hop_typeinv_mut_ref with the overwrite deleted: `caller`
//@ mechanism: borrows its own parameter, whose invariant it holds, so the clause owed where
//@ mechanism: `T` is fixed discharges from that premise (D-141). The twin differing in the value
//@ mechanism: alone is `..._value_control`, which cannot be discharged yet.
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

pub trait Bump {
    #[ensures(result@ == 10)]
    fn total_mut(&mut self) -> i32;
}

impl Bump for Sum10 {
    fn total_mut(&mut self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Bump>(t: &mut T) -> i32 {
    t.total_mut()
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    via(&mut s)
}
