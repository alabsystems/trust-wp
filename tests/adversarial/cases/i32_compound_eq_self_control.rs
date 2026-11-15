//@ expect: verify
//@ mechanism: the isolating twin of f32_compound_eq_self_despite_nan.rs: the same four functions and
//@ mechanism: contracts over `i32`, whose `==` is logical equality, so the builtin `PartialEq` contracts are
//@ mechanism: admitted and true. Only the scalar type differs.
//@ accept-means: n/a (control) — a value built from integers equals itself.
//@ fixed-by: n/a (control)
//@ teeth: verified before and after D-215 (each function verified).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(!result)]
pub fn opt_ne_self(x: i32) -> bool {
    let o = Some(x);
    o != o
}

#[ensures(result)]
pub fn tup_eq_self(x: i32, y: i32) -> bool {
    let p = (x, y);
    p == p
}

#[ensures(result)]
pub fn arr_eq_self(x: i32) -> bool {
    let a = [x, x];
    a == a
}

#[ensures(result)]
pub fn ref_eq_self(x: i32) -> bool {
    let r = &x;
    r == r
}
