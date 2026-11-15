//@ expect: verify
//@ xfail: D-141's price: an impl of a foreign trait's method holds no parameter premise, since drop
//@ xfail: glue runs it and owes nothing, so `drop`, dividing by a value only the invariant bounds, is
//@ xfail: refuted. (`dropper` is refused besides, with the route arms knobbed off too.)
//@ xfail-verdict: failed
//@ mechanism: the TRUE twin of drop_glue_vec_element_typeinv_uncharged.rs: every element keeps its
//@ mechanism: invariant.
//@ teeth: control — `drop` verified with the three route arms knobbed off, `dropper` unknown there.
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

impl Drop for Sum10 {
    fn drop(&mut self) {
        let r = self.a + self.b;
        let _q = 100 / (r - 2);
    }
}

#[ensures(result@ == x@)]
pub fn dropper(x: u8) -> u8 {
    let _v = vec![Sum10 { a: 3, b: 7 }];
    x
}
