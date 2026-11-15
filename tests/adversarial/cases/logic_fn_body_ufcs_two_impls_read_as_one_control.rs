//@ expect: verify
//@ mechanism: control for logic_fn_body_ufcs_two_impls_read_as_one, differing in the `+ 1` alone: each qualified call is read as its own implementation, and `y + 1 == y + 1` holds.
//@ accept-means: n/a (control) — `<S as Tr>::m(y)` is `<U as Tr>::m(y) + 1`.
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
    <S as Tr>::m(y) == <U as Tr>::m(y) + 1
}
