//@ expect: verify
//@ xfail: D-141's price: an impl of a foreign trait's method holds no parameter premise, since std
//@ xfail: reaches it from code no lane walks, so `clone`, dividing by a value only the invariant
//@ xfail: bounds, is refuted. (`caller` is refused besides, with the route arms knobbed off too.)
//@ xfail-verdict: failed
//@ mechanism: the TRUE twin of std_vec_clone_to_local_clone_typeinv_uncharged.rs: every element keeps
//@ mechanism: its invariant.
//@ teeth: control — `clone` verified with the three route arms knobbed off, `caller` unknown there.
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

impl Clone for Sum10 {
    fn clone(&self) -> Sum10 {
        let r = self.a + self.b;
        let _q = 100 / (r - 2);
        Sum10 { a: self.a, b: self.b }
    }
}

#[ensures(true)]
pub fn caller() -> usize {
    let v = vec![Sum10 { a: 3, b: 7 }];
    let w = v.clone();
    w.len()
}
