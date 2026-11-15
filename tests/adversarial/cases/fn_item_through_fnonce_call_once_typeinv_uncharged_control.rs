//@ expect: verify
//@ xfail: the price of D-141's `Fn*` route closure. A fn item whose body holds a parameter invariant
//@ xfail: premise, called through the `Fn*` trait's own method, keeps that spec's opaque
//@ xfail: `precondition`, which no proof discharges, so `caller` is FAILED on a TRUE program. Closing
//@ xfail: it means stating the grant at this route, instantiated at the item's generic arguments,
//@ xfail: beside the written `requires`. The stable spellings (`let f = &take; f(s)`) are charged
//@ xfail: through another lane and verify.
//@ xfail-verdict: failed
//@ mechanism: the TRUE twin of fn_item_through_fnonce_call_once_typeinv_uncharged.rs: the value
//@ mechanism: `caller` hands `take` through `FnOnce::call_once` keeps its invariant, so `take` returns 10
//@ mechanism: and a fix that charges the grant at this route must verify it.
//@ teeth: control — verified on the build with the fix knobbed off, `caller` FAILED with it on.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(fn_traits, unboxed_closures)]

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

#[ensures(result@ == 10)]
pub fn take(t: Sum10) -> i32 {
    let r = t.a + t.b;
    100 / (r - 2) + 10 - 100 / (r - 2)
}

#[ensures(result@ == 10)]
pub fn caller() -> i32 {
    FnOnce::call_once(take, (Sum10 { a: 3, b: 7 },))
}
