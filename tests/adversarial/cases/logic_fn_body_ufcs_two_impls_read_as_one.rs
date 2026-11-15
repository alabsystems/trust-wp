//@ expect: reject
//@ mechanism: one trait method, two implementations, both called in one logic body by their qualified paths: `<S as Tr>::m(y) == <U as Tr>::m(y)`. Both calls are spelled `m` and rustc names one trait method for both, with the implementations that run told apart by the self type only; read as one uninterpreted `m`, the body is `m(y) == m(y)`. Each qualified call must be read as its own implementation. Found probing sideways from D-120.
//@ accept-means: a logic function whose body compares two implementations of one trait method is credited with their equality, and the crate exits 0.
//@ WHY IT IS FALSE: `<S as Tr>::m(y)` is `y + 1` and `<U as Tr>::m(y)` is `y`.
//@ teeth: UNVERIFIED, a shape gate: refuted with D-120 open and with D-136, and the control verifies at both; it pins that a record keyed by the trait method rustc names does not merge the two implementations. The control is logic_fn_body_ufcs_two_impls_read_as_one_control.rs.
//@ verdict: error
//@ refused-with: creusot_test::caller postcondition FAILED (logic postcondition)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn m(x: Int) -> Int;
}

pub struct S;

impl Tr for S {
    #[logic(open)]
    fn m(x: Int) -> Int {
        x + 1
    }
}

pub struct U;

impl Tr for U {
    #[logic(open)]
    fn m(x: Int) -> Int {
        x
    }
}

#[logic]
#[ensures(result)]
pub fn caller(y: Int) -> bool {
    <S as Tr>::m(y) == <U as Tr>::m(y)
}
