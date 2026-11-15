//@ expect: verify
//@ mechanism: `Ghost::borrow` and `Ghost::borrow_mut` are specified as the ghost itself (`result == self`,
//@ mechanism: no precondition), and program code calls them (Creusot's `open(inv.borrow(), ..)`).
//@ mechanism: Their run-time bodies panicked ("Ghost::borrow called at runtime"), so this contract
//@ mechanism: was FALSE while it verified; they now return the zero-sized ghost handle, as Creusot's
//@ mechanism: `#[erasure(_)]` borrow, and it is TRUE.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: D-139 — the run-time borrow is the zero-sized handle.
//@ teeth: ACCEPTED as a reject case when committed (`f verified`, `g verified`, exit 0; natively both
//@ teeth: calls panicked); verified under D-139, where natively neither panics.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f() {
    let g = ghost!(5i32);
    let _b = g.borrow();
}

#[ensures(true)]
pub fn g() {
    let mut g = ghost!(5i32);
    let _b = g.borrow_mut();
}
