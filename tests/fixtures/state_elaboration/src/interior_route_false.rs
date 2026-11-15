// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A `&mut` parameter over interior-mutable memory is written by whoever
//! holds a shared reference into its referent, by routes the lanes did not
//! all see: inside an annotated loop, and through a `&Cell` copied out of the
//! referent. Every function below leaves the cell 5 and claims `^x == *x`:
//! every contract is false except `inc_beside_cell`'s.

#![allow(unused)]
#![feature(stmt_expr_attributes, proc_macro_hygiene)]

use std::cell::Cell;

use trust_wp::prelude::*;

#[ensures(^x == *x)]
pub fn loop_set(x: &mut Cell<i32>) {
    let mut i = 0i32;
    #[invariant(true)]
    while i < 1 {
        x.set(5);
        i += 1;
    }
}

pub struct S<'a> {
    pub c: &'a Cell<i32>,
}

#[ensures(^x == *x)]
pub fn copy_field_set(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(^x == *x)]
pub fn copy_option_set(x: &mut Option<&Cell<i32>>) {
    if let Some(c) = *x {
        c.set(5);
    }
}

// TRUE: `n` is not over interior-mutable memory.
#[requires(*n < 100i32)]
#[ensures(^n == *n + 1i32)]
pub fn inc_beside_cell(n: &mut i32, x: &mut Cell<i32>) {
    *n += 1;
}

fn main() {}
