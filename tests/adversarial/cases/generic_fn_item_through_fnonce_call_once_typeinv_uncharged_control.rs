//@ expect: verify
//@ xfail: the price of D-141's `Fn*` route closure, generic spelling: `via` holds a type-parameter
//@ xfail: invariant premise, so `FnOnce::call_once(via::<Sum10>, ..)` keeps the `Fn*` spec's opaque
//@ xfail: `precondition` and `caller` is FAILED on a TRUE program. Closing it means stating the grant
//@ xfail: at this route, instantiated at `Sum10`, beside the written `requires`.
//@ xfail-verdict: failed
//@ mechanism: the TRUE twin of generic_fn_item_through_fnonce_call_once_typeinv_uncharged.rs: the
//@ mechanism: value `caller` hands `via::<Sum10>` keeps its invariant, so the impl returns 10.
//@ teeth: control — verified on the build with the fix knobbed off, `caller` FAILED with it on;
//@ teeth: `unknown` on wp-campaign's code, where `via`'s hop is refused under D-75.
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

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self) -> i32;
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<T: Total>(t: T) -> i32 {
    let r = t.total();
    100 / (r - 2) + 10 - 100 / (r - 2)
}

#[ensures(result@ == 10)]
pub fn caller() -> i32 {
    FnOnce::call_once(via::<Sum10>, (Sum10 { a: 3, b: 7 },))
}
