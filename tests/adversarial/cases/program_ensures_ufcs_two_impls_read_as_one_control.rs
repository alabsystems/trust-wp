//@ expect: verify
//@ mechanism: control for program_ensures_ufcs_two_impls_read_as_one.rs, differing in the `+ 1` alone: each qualified call is read as its own implementation, and `x@ + 1 == x@ + 1` holds. Refused (`unknown`) where path calls are matched with rustc's by first argument (the two share `x@`); verified where each is matched by its written path.
//@ accept-means: n/a (control) — `<S as Tr>::m(x@)` is `<U as Tr>::m(x@) + 1`.
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

#[ensures(<S as Tr>::m(x@) == <U as Tr>::m(x@) + 1)]
pub fn prog(x: u32) {}
