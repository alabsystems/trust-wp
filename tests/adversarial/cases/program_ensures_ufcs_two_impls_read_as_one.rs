//@ expect: reject
//@ mechanism: the contract-clause spelling of logic_fn_body_ufcs_two_impls_read_as_one: `<S as Tr>::m(x@) == <U as Tr>::m(x@)` in a program function's `ensures`. Both calls are spelled `m` and name one trait method; read as one uninterpreted `m`, the clause is `m(x@) == m(x@)`. Found probing sideways from D-120.
//@ accept-means: a program function is credited with the equality of two implementations of one trait method, and the crate exits 0.
//@ WHY IT IS FALSE: `<S as Tr>::m(x@)` is `x@ + 1` and `<U as Tr>::m(x@)` is `x@`.
//@ teeth: UNVERIFIED, a shape gate: refuted with D-120 open and with D-136; it pins that the clause reads each qualified call as its own implementation.
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

#[ensures(<S as Tr>::m(x@) == <U as Tr>::m(x@))]
pub fn prog(x: u32) {}
