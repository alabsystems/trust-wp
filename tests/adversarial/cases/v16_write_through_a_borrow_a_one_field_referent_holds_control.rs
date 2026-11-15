//@ expect: verify
//@ mechanism: the true contracts beside v16_write_through_a_borrow_a_one_field_referent_holds that
//@ mechanism: D-184 must leave credited: a one-field holder the body does not write, a read of the
//@ mechanism: borrow it holds, a BY-VALUE one-field newtype written through (its own final value,
//@ mechanism: D-183 leaves `^x.0` of a by-value holder read), and a one-field referent holding no
//@ mechanism: borrow written as a value carrier.
//@ accept-means: (control) these verify.
//@ teeth: MEASURED (debug driver, ay aba6406be, clean ae4c8f59e): c4, c6, c7 and c8 verified on
//@ teeth: a76f9b72 and with D-184 (c7 was once an evidence gap, proof-trusted, on a76f9b72 in an
//@ teeth: earlier run).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub struct N<'a>(pub &'a mut i32);

pub struct W {
    pub a: i32,
}

#[ensures(^x.0 == 5i32)]
pub fn c4(x: N<'_>) {
    *x.0 = 5i32;
}

#[ensures((^x).a == 5i32)]
pub fn c6(x: &mut W) {
    x.a = 5i32;
}

#[ensures(*(^x).m == *(*x).m)]
pub fn c7(x: &mut M<'_>) {}

#[ensures(result == *(*x).m)]
pub fn c8(x: &mut M<'_>) -> i32 {
    *x.m
}
