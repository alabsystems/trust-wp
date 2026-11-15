//@ expect: reject
//@ verdict: error
//@ refused-with: as Deref>` runs outside ghost!(...) and snapshot!(...)
//@ also-verified: read_borrow
//@ mechanism: the holder check refuses a call whose own where-clauses ask `Deref` or `Borrow` of a
//@ mechanism: `Ghost` (ghost_holder_generic_bound_in_program_context_panics), and reads nothing past
//@ mechanism: them. A bound on a trait of the crate's own whose supertrait is `Deref` or `Borrow`
//@ mechanism: (`T: ReadsI32` with `trait ReadsI32: Deref<Target = i32>`) asks the same of the
//@ mechanism: instance, so given a `Ghost<i32>` or a `Ghost<Box<i32>>` the generic body runs
//@ mechanism: `<Ghost<i32> as Deref>::deref` or `<Ghost<Box<i32>> as Borrow<i32>>::borrow`, and each
//@ mechanism: panics. The call site owes that the instance it picks does not.
//@ accept-means: the program bodies that hand a ghost to a function bounded by a trait whose supertrait
//@ accept-means: is `Deref` or `Borrow` are credited `verified`, though each call panics.
//@ fixed-by: D-193: the bounds a call asks are read with their supertraits, the bounds of their traits'
//@ fixed-by: associated types and the where-clauses of the impls rustc selects for them
//@ fixed-by: (`program_context::asked_trait_bounds`), so `Ghost<i32>: ReadsI32` asks `Deref` of the ghost.
//@ WHY THE CONTRACT IS FALSE: `call_deref` and `call_borrow` panic on every call ("Ghost deref called
//@ WHY THE CONTRACT IS FALSE: at runtime", "Ghost<Box<T>>::borrow called at runtime"). `read_borrow`'s
//@ WHY THE CONTRACT IS FALSE: credit is the modular one: its `true` holds for every instance whose
//@ WHY THE CONTRACT IS FALSE: `borrow` does not panic, which the caller owes.
//@ teeth: at wp-s150 9c6178f1, `call_deref` and `call_borrow` verified (`read_deref` FAILED,
//@ teeth: `read_borrow` verified). Natively, built against trust-wp-std, both callers panic in the
//@ teeth: callee. Refused at wp-s150's fix; ghost_holder_harmless_elaborated_bound_control, a ghost given
//@ teeth: through a `Debug` or `Clone` supertrait, verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::{borrow::Borrow, ops::Deref};

pub trait ReadsI32: Deref<Target = i32> {}
impl<T: Deref<Target = i32>> ReadsI32 for T {}

pub trait LendsI32: Borrow<i32> {}
impl<T: Borrow<i32>> LendsI32 for T {}

#[ensures(true)]
pub fn read_deref<T: ReadsI32>(x: &T) -> i32 {
    **x
}

#[ensures(true)]
pub fn read_borrow<T: LendsI32>(x: &T) -> i32 {
    *x.borrow()
}

#[ensures(true)]
pub fn call_deref() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    read_deref(&g)
}

#[ensures(true)]
pub fn call_borrow() -> i32 {
    let g: Ghost<Box<i32>> = ghost!(Box::new(5i32));
    read_borrow(&g)
}
