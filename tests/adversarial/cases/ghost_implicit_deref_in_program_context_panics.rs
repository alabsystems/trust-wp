//@ expect: reject
//@ verdict: error
//@ refused-with: a ghost value is dereferenced outside ghost!(...) by a `Deref` the compiler inserts
//@ mechanism: the program-context validator refuses an explicit `*g` or `g.deref()` of a `Ghost`, but
//@ mechanism: not the `Deref` rustc inserts itself: a deref coercion (`let r: &i32 = &g`), a field read
//@ mechanism: through a ghost (`g.0`), a method call on the ghost's contents (`g.abs()`, `own.val()`).
//@ mechanism: Each is a run-time call of `<Ghost<T> as Deref>::deref`, which panics ("Ghost deref
//@ mechanism: called at runtime"), and the verifier reads it as the identity.
//@ accept-means: each function panics on every call while its contract is reported verified.
//@ fixed-by: D-139 — the program-context validator reads the compiler's deref adjustments.
//@ teeth: ACCEPTED (all four `verified`, exit 0) when committed; natively each panics. Refused at
//@ teeth: each of the four under D-139.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(result == 5)]
pub fn coerce() -> i32 {
    let g = ghost!(5i32);
    let r: &i32 = &g;
    *r
}

#[ensures(result == 5)]
pub fn field() -> i32 {
    let g = ghost!((5i32, 6i32));
    g.0
}

#[ensures(result == 5)]
pub fn method() -> i32 {
    let g = ghost!(5i32);
    g.abs()
}

#[ensures(true)]
pub fn perm_val() {
    let (_p, own) = Perm::new(1i32);
    let _v: &i32 = own.val();
}
