//@ expect: reject
//@ verdict: error
//@ refused-with: as Borrow>` runs outside ghost!(...) and snapshot!(...)
//@ also-verified: by_borrow
//@ mechanism: D-133 refuses, in program code, a call whose bounds ask a type holding a `Ghost` or
//@ mechanism: `Snapshot` for a comparison or `Hash`. A generic function of the crate's own, bounded by
//@ mechanism: `Borrow` or `Deref`, is verified once for every `T` and reads `x.borrow()` and `**x` as
//@ mechanism: calls with no precondition; given a `Ghost<Box<i32>>` or a `Ghost<i32>`, its body runs
//@ mechanism: `<Ghost<Box<i32>> as Borrow<i32>>::borrow` or `<Ghost<i32> as Deref>::deref`, and each
//@ mechanism: panics. The call site owes that the instance it picks does not, and the holder check does
//@ mechanism: not ask `Borrow` or `Deref`.
//@ accept-means: the program bodies that hand a ghost to a `Borrow`- or `Deref`-bounded function are
//@ accept-means: credited `verified`, though each call panics.
//@ fixed-by: D-193: a call whose instantiated bounds ask `Borrow`, `BorrowMut`, `Deref` or `DerefMut` of
//@ fixed-by: a `Ghost` or `Snapshot` itself is refused in code that runs; trust-wp-std's own permission
//@ fixed-by: APIs, whose bodies never borrow, stay open.
//@ WHY THE CONTRACT IS FALSE: `call_borrow` and `call_deref` panic on every call ("Ghost<Box<T>>::borrow
//@ WHY THE CONTRACT IS FALSE: called at runtime", "Ghost deref called at runtime"). `by_borrow`'s credit
//@ WHY THE CONTRACT IS FALSE: is the modular one: its `true` holds for every instance whose `borrow` does
//@ WHY THE CONTRACT IS FALSE: not panic, which the caller owes.
//@ teeth: at the campaign base 6e6bf5f3, `call_borrow` and `call_deref` verified (`by_deref` FAILED,
//@ teeth: `by_borrow` verified). Natively, built against trust-wp-std, both callers panic in the callee.
//@ teeth: Refused at wp-s150; ghost_holder_generic_bound_on_holder_control, a `Box` holding the ghost
//@ teeth: given to a `Borrow`-bounded function, verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::{borrow::Borrow, ops::Deref};

#[ensures(true)]
pub fn by_borrow<T: Borrow<i32>>(x: &T) -> i32 {
    *x.borrow()
}

#[ensures(true)]
pub fn by_deref<T: Deref<Target = i32>>(x: &T) -> i32 {
    **x
}

#[ensures(true)]
pub fn call_borrow() -> i32 {
    let g: Ghost<Box<i32>> = ghost!(Box::new(5i32));
    by_borrow(&g)
}

#[ensures(true)]
pub fn call_deref() -> i32 {
    let g: Ghost<i32> = ghost!(5i32);
    by_deref(&g)
}
