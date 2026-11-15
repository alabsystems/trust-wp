//@ expect: reject
//@ mechanism: D-107 moved a `&mut` parameter's final value when the mut-borrow lane saw a shared
//@ mechanism: borrow of its referent that exposes interior mutability (`x.set(5)`). An annotated
//@ mechanism: loop is framed by `loops::changed_places::extract_modified_vars` /
//@ mechanism: `loops::write_sites`, which count stores, call destinations and `&mut`/raw borrows
//@ mechanism: only, so the same write inside `#[invariant(true)] while ..` left `x` out of the
//@ mechanism: loop's modified set and the post-loop path kept its entry value as its final value.
//@ accept-means: a write through interior mutability reachable from a `&mut` parameter is
//@ accept-means: invisible to the value that parameter is left with when it happens in a loop.
//@ WHY THE CONTRACT IS FALSE: each loop runs once and leaves the cell holding 5, whatever it held
//@ WHY THE CONTRACT IS FALSE: at entry (the reading v9_interior_write_through_shared_reborrow's
//@ WHY THE CONTRACT IS FALSE: `direct_set_cell` and `boxed_set` are refused under).
//@ fixed-by: D-108 (a `&mut` parameter over interior-mutable memory has no final value to state,
//@ fixed-by: in either lane, whatever route writes it)
//@ teeth: MEASURED (debug driver): f6039647 verifies all three functions ("loop invariant +
//@ teeth: call obligations verified", then "verified"); on D-108 each clause is refused by name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(stmt_expr_attributes, proc_macro_hygiene)]

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn loop_set(x: &mut Cell<i32>) {
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        x.set(5);
        i += 1;
    }
}

pub struct H {
    pub c: Box<Cell<i32>>,
}

#[ensures(^x == *x)]
pub fn loop_boxed_field_set(x: &mut H) {
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        x.c.set(5);
        i += 1;
    }
}

#[ensures(*x == old(*x))]
pub fn loop_set_old(x: &mut Cell<i32>) {
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        x.set(5);
        i += 1;
    }
}
