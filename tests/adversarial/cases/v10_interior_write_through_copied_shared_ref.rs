//@ expect: reject
//@ mechanism: D-107 havocked a `&mut` parameter when a SHARED BORROW of its referent exposed
//@ mechanism: interior mutability (`x.c.set(5)` borrows `&*x.c`). Copying the `&Cell<i32>` the
//@ mechanism: referent holds out BY VALUE (`let c = x.c;`, a tuple, `Option` or array element) is
//@ mechanism: no borrow of a tracked place, so the parameter kept its entry value as its final
//@ mechanism: value while `c.set(5)` wrote the cell that value holds.
//@ accept-means: a write through interior mutability reachable from a `&mut` parameter's referent
//@ accept-means: is invisible to the value that parameter is left with when the shared reference
//@ accept-means: is copied out first.
//@ WHY THE CONTRACT IS FALSE: each body leaves the cell the referent holds at 5, whatever it held
//@ WHY THE CONTRACT IS FALSE: at entry (the same reading as v9_interior_write_through_shared_reborrow,
//@ WHY THE CONTRACT IS FALSE: whose `field_set` differs from `copy_field_set` only by the copy).
//@ fixed-by: D-108 (a `&mut` parameter over interior-mutable memory has no final value to state,
//@ fixed-by: in either lane, whatever route writes it)
//@ teeth: MEASURED (debug driver): f6039647 verifies all five functions (it answered `unknown`
//@ teeth: for the method spelling `x.c.set(5)`); on D-108 each clause is refused by name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

pub struct S<'a> {
    pub c: &'a Cell<i32>,
}

#[ensures(^x == *x)]
pub fn copy_field_set(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(^x == *x)]
pub fn copy_tuple_set(x: &mut (u8, &Cell<i32>)) {
    let (_, c) = *x;
    c.set(5);
}

#[ensures(^x == *x)]
pub fn copy_option_set(x: &mut Option<&Cell<i32>>) {
    if let Some(c) = *x {
        c.set(5);
    }
}

#[ensures(^x == *x)]
pub fn copy_option_match(x: &mut Option<&Cell<i32>>) {
    match *x {
        Some(c) => c.set(5),
        None => {}
    }
}

#[ensures(^x == *x)]
pub fn copy_array_set(x: &mut [&Cell<i32>; 1]) {
    let c = x[0];
    c.set(5);
}
