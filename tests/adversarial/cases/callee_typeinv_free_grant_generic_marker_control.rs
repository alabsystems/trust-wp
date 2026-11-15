//@ expect: verify
//@ mechanism: the TRUE twin of callee_typeinv_free_grant_generic_marker. Same callee, same
//@ mechanism: marker path, and an argument the caller cannot be shown to break because it
//@ mechanism: is the caller's OWN parameter, which carries the same invariant as a premise.
//@ mechanism: It is what says the reject twin rejects because the invariant is broken and
//@ mechanism: not because the obligation is unprovable for every argument.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Meas {
    #[logic]
    fn meas(self) -> Int;
}

pub struct Unit;

impl Meas for Unit {
    #[logic(open)]
    fn meas(self) -> Int {
        pearlite! { 0 }
    }
}

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

#[ensures(result@ == 10)]
#[ensures(t.meas() == t.meas())]
pub fn total<T: Meas>(t: T, s: Sum10) -> i32 {
    s.a + s.b
}

#[ensures(result@ == 10)]
pub fn caller(s: Sum10) -> i32 {
    total(Unit, s)
}
