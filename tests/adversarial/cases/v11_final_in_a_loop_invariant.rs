//@ expect: reject
//@ mechanism: The encoder read `resolve(x)` as the trivially true resolve of a by-value parameter
//@ mechanism: whenever the lane had no `x_final` symbol under its prefix. A loop head has none, so
//@ mechanism: `#[invariant(resolve(x))]` was established and preserved as `true` while `^x == *x`
//@ mechanism: in the same place is read as a final value. `resolve` of a borrow is now encoded as
//@ mechanism: the `*x == ^x` it denotes, through the lane's own final reading; by-value is read
//@ mechanism: from the variable's sort, never from a missing symbol.
//@ accept-means: a loop invariant stating a borrow's final value is credited as `true` when it is
//@ accept-means: spelled `resolve`.
//@ WHY THE CONTRACT IS FALSE: each loop leaves the borrow (the cell its referent reaches) at 5 and
//@ WHY THE CONTRACT IS FALSE: nothing writes it after the loop, so at the first loop head `*x` is
//@ WHY THE CONTRACT IS FALSE: the entry value, which is not 5, and `^x` is 5: `resolve(x)` does not
//@ WHY THE CONTRACT IS FALSE: hold there.
//@ fixed-by: D-109 (`resolve` of a borrow is the final value it denotes in every lane)
//@ teeth: MEASURED (debug driver, ay 0e44aed6a): 9da9f9a8 verifies both functions (loop invariant +
//@ teeth: call obligations); on D-109 each loop invariant is FAILED, as `^x == *x` there is.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

#[requires(*x != 5i32)]
pub fn plain_set(x: &mut i32) {
    let mut i = 0i32;
    #[invariant(resolve(x))]
    while i < 1 {
        *x = 5;
        i += 1;
    }
}

pub struct S<'a> {
    pub c: &'a Cell<i32>,
}

pub fn copy_set(x: &mut S<'_>) {
    let mut i = 0i32;
    #[invariant(resolve(x))]
    while i < 1 {
        let c = x.c;
        c.set(5);
        i += 1;
    }
}
