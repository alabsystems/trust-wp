//@ expect: reject
//@ verdict: error
//@ refused-with: as Borrow>` runs outside ghost!(...) and snapshot!(...)
//@ also-verified: <T as Get>::get
//@ mechanism: the holder check reads the bounds a call's callee states, and those of the impl the call
//@ mechanism: itself resolves to, but not those of an impl a bound selects. `go<T: Get>` asks only
//@ mechanism: `T: Get`; the instance `Ghost<Box<i32>>` meets it through the blanket
//@ mechanism: `impl<T: Borrow<i32>> Get for T`, whose `get` runs `<Ghost<Box<i32>> as Borrow<i32>>::borrow`,
//@ mechanism: which panics. The call site owes the bounds of the impl it selects.
//@ accept-means: a program body that hands a ghost to a function whose bound is met by a blanket impl
//@ accept-means: asking `Borrow` is credited `verified`, though the call panics.
//@ fixed-by: D-193: a bound a call asks is read through the impl rustc selects for it, to that impl's
//@ fixed-by: own where-clauses (`program_context::asked_trait_bounds`).
//@ WHY THE CONTRACT IS FALSE: `caller` panics on every call ("Ghost<Box<T>>::borrow called at
//@ WHY THE CONTRACT IS FALSE: runtime"). `<T as Get>::get`'s credit is the modular one: its `true` holds
//@ WHY THE CONTRACT IS FALSE: for every instance whose `borrow` does not panic, which the caller owes.
//@ teeth: at wp-s150 9c6178f1, `caller` verified (`go` unknown on a fail-closed `false`).
//@ teeth: Natively, built against trust-wp-std, `caller` panics in the blanket impl's `get`. Refused at
//@ teeth: wp-s150's fix; ghost_holder_harmless_elaborated_bound_control, a ghost meeting a blanket impl
//@ teeth: whose where-clause asks `Debug`, verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::borrow::Borrow;

pub trait Get {
    fn get(&self) -> i32;
}

impl<T: Borrow<i32>> Get for T {
    #[ensures(true)]
    fn get(&self) -> i32 {
        *self.borrow()
    }
}

#[ensures(true)]
pub fn go<T: Get>(x: &T) -> i32 {
    x.get()
}

#[ensures(true)]
pub fn caller() -> i32 {
    let g: Ghost<Box<i32>> = ghost!(Box::new(5i32));
    go(&g)
}
