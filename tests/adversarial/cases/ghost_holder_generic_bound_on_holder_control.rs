//@ expect: verify
//@ mechanism: the TRUE twin of ghost_holder_generic_bound_in_program_context_panics: the same
//@ mechanism: `Borrow`-bounded function given a `Box` holding the ghost asks `Borrow` of the `Box`
//@ mechanism: (`impl<T> Borrow<T> for T`), whose body returns the reference without running the
//@ mechanism: ghost's own `borrow`. Only a `Deref` or `Borrow` asked of a `Ghost` itself panics.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — natively `call_borrow` returns; verified before and after the holder check asks
//@ teeth: `Borrow`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::borrow::Borrow;

#[ensures(true)]
pub fn by_borrow<T: Borrow<Ghost<i32>>>(x: &T) -> usize {
    let _g: &Ghost<i32> = x.borrow();
    0
}

#[ensures(true)]
pub fn call_borrow() -> usize {
    let g: Ghost<i32> = ghost!(5i32);
    by_borrow(&Box::new(g))
}
