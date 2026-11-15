// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A shared borrow of a `&mut` parameter's referent from which interior-mutable
//! memory is reachable writes that referent: `x.set(5)` borrows `&*x`. The
//! final value read back once ignored every such write, so `^x == *x` held of
//! each function below: every contract is false.

#![allow(unused)]

use std::cell::Cell;

use trust_wp::prelude::*;

// FALSE: the cell is left 5.
#[ensures(^x == *x)]
pub fn direct_set_cell(x: &mut Cell<i32>) {
    x.set(5);
}

// FALSE: the cell is left 5.
#[ensures(^x == *x)]
pub fn local_reborrow_set(x: &mut Cell<i32>) {
    let y = &mut *x;
    y.set(5);
}

// FALSE: the cell is left 5.
#[ensures(^x == *x)]
pub fn boxed_set(x: &mut Box<Cell<i32>>) {
    x.set(5);
}

pub struct H {
    pub c: Cell<i32>,
}

// FALSE: the cell is left 5.
#[ensures(^x == *x)]
pub fn field_set(x: &mut H) {
    x.c.set(5);
}

// FALSE: the cell is left 5.
#[ensures(*x == old(*x))]
pub fn old_dialect_set(x: &mut Cell<i32>) {
    x.set(5);
}

fn main() {}
