//@ expect: verify
//@ xfail: D-141's price: `hop` is a target, and a `dyn` call cannot state the grant of the body it
//@ xfail: enters, so the call is refused whatever the boxed value holds.
//@ xfail-verdict: unknown
//@ mechanism: the TRUE twin of contractless_caller_dyn_local_trait_typeinv_unexamined.rs: the boxed
//@ mechanism: value keeps its invariant.
//@ teeth: control — verified with the three route arms knobbed off, where `hop` was examined by nothing.
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

pub trait Tr {
    fn m(&self) -> i32;
}

impl Tr for Sum10 {
    fn m(&self) -> i32 {
        let r = self.a + self.b;
        100 / (r - 2)
    }
}

pub fn hop() -> i32 {
    let b: Box<dyn Tr> = Box::new(Sum10 { a: 3, b: 7 });
    b.m()
}
