//@ expect: verify
//@ mechanism: the TRUE twin of contractless_generic_loop_lane_premise_without_table_entry.rs:
//@ mechanism: `hop` hands `via` a `Sum10` whose invariant holds.
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
    fn total(&self) -> i32;
}

impl Total for Sum10 {
    fn total(&self) -> i32 {
        self.a + self.b
    }
}

pub fn via<T: Total>(t: T, n: u32) -> i32 {
    let mut r = 10;
    let mut i = 0;
    #[invariant(r@ == 10)]
    while i < n {
        r = t.total();
        i += 1;
    }
    r
}

pub fn hop() -> i32 {
    via(Sum10 { a: 3, b: 7 }, 1)
}
