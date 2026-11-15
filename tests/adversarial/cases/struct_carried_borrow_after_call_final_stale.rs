//@ expect: reject
//@ mechanism: the escape spelling of returned_borrow_after_call_final_stale.rs, with the
//@ mechanism: borrow leaving inside a struct instead of on its own. It says the hole is
//@ mechanism: about the borrow OUTLIVING the body — about `^x` being decided by whoever
//@ mechanism: holds the borrow next — and not about the bare `return x` statement shape.
//@ accept-means: any escape route for a `&mut` parameter preserves a call's prophecy
//@ accept-means: credit, so the credit rule cannot be closed by enumerating return
//@ accept-means: statements either.
//@ WHY THE PROGRAM IS WRONG: the caller holds `result.r`, which is the borrow of `*x`;
//@ WHY THE PROGRAM IS WRONG: writing 7 through it leaves `^x == 7`. The contract claims 1.
//@ fixed-by: D-80
//@ teeth: LIVE: ACCEPTED, alongside returned_borrow_after_call_final_stale.rs.
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W<'a> {
    pub r: &'a mut i32,
}

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn f(x: &mut i32) -> W<'_> {
    set(x);
    W { r: x }
}
