//@ expect: verify
//@ mechanism: control for program_ensures_logic_fn_body_one_spelling_two_definitions, differing in the block's rename alone: both `k(y)` calls denote `one`, rustc resolves both to it, the body is read as `one(y) == one(y)`, and `prog`'s `ensures` holds.
//@ accept-means: n/a (control) — `same(y)` is `1 == 1`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn zero(x: Int) -> Int {
    0
}

#[logic]
pub fn one(x: Int) -> Int {
    1
}

use crate::one as k;

#[logic(open)]
pub fn same(y: Int) -> bool {
    let a = {
        use crate::one as k;
        k(y)
    };
    a == k(y)
}

#[ensures(same(x@))]
pub fn prog(x: u32) {}
