//@ expect: reject
//@ mechanism: `x.set(5)` on an `x: &mut Cell<i32>` borrows `&*x` shared and writes the cell
//@ mechanism: through it. The mut-borrow lane tracked only `&mut` and `*mut` aliases of a
//@ mechanism: parameter's referent, so the shared reborrow was no write and the final value it
//@ mechanism: read back was the entry value: `^x == *x` held of every function below.
//@ accept-means: a write through interior mutability reachable from a `&mut` parameter's
//@ accept-means: referent (inline, behind a `Box`, in a field, through a helper) is invisible to
//@ accept-means: the value that parameter is left with.
//@ WHY THE CONTRACT IS FALSE: each body leaves the cell holding 5, whatever it held at entry.
//@ fixed-by: D-107 (a shared borrow of a tracked referent from which interior-mutable memory is
//@ fixed-by: reachable, `extract::ty_exposes_interior_mutability`, havocs the parameter)
//@ teeth: MEASURED (debug driver) on 576532d7: `direct_set_cell`, `local_reborrow_set`,
//@ teeth: `boxed_set` and `field_set` verified (`helper_set` unknown). On the D-107 tree all
//@ teeth: five are unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn direct_set_cell(x: &mut Cell<i32>) {
    x.set(5);
}

#[ensures(^x == *x)]
pub fn local_reborrow_set(x: &mut Cell<i32>) {
    let y = &mut *x;
    y.set(5);
}

#[ensures(^x == *x)]
pub fn boxed_set(x: &mut Box<Cell<i32>>) {
    x.set(5);
}

pub struct H {
    pub c: Cell<i32>,
}

#[ensures(^x == *x)]
pub fn field_set(x: &mut H) {
    x.c.set(5);
}

pub fn setter(c: &Cell<i32>) {
    c.set(5);
}

#[ensures(*x == old(*x))]
pub fn helper_set(x: &mut Cell<i32>) {
    setter(x);
}
