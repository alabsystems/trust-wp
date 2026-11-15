//@ expect: reject
//@ verdict: error
//@ refused-with: `Borrow`/`BorrowMut` of a `Ghost` panics at run time
//@ mechanism: trust-wp-std implements `Borrow<T>` and `BorrowMut<T>` for `Ghost<Box<T>>`, and both
//@ mechanism: panic at run time ("Ghost<Box<T>>::borrow_mut called at runtime"). A call through the
//@ mechanism: trait in program code is not one the validator counts as an extraction, and nothing in
//@ mechanism: the verifier owes its panic. Creusot's `Ghost` implements neither trait.
//@ accept-means: `f` panics on every call while its contract is reported verified.
//@ fixed-by: D-139 — a `Borrow`/`BorrowMut` call on a ghost in program code is refused.
//@ teeth: ACCEPTED (`f verified`, exit 0) when committed, measured on this head's tree with the
//@ teeth: validator changes then uncommitted, none of which reads the `Borrow` traits. Refused
//@ teeth: under D-139.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::borrow::BorrowMut;

#[ensures(true)]
pub fn f() {
    let mut x = ghost!(Box::new(5i32));
    let r: &mut i32 = BorrowMut::<i32>::borrow_mut(&mut x);
    *r = 6;
}
