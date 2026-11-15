//@ expect: reject
//@ mechanism: `==`/`!=` over an `Option`, a tuple, an array or a reference of `f32` run the library impl,
//@ mechanism: which compares the `f32`s with IEEE `==`: false of NaN. The builtin `PartialEq` contracts
//@ mechanism: state `result == (self@ == rhs@)` / `(self@ != rhs@)`, logical equality, which is true of
//@ mechanism: NaN. D-215 withholds them from a comparison whose type arguments carry a float, and from a
//@ mechanism: library impl whose `T: PartialEq` bound a float discharges. The `f32` spellings of
//@ mechanism: f64_option_eq_reflexive.rs, f64_tuple_eq_reflexive.rs and f64_array_eq_reflexive.rs, with
//@ mechanism: `!=` for the `Option` and a reference beside them.
//@ accept-means: at `x = f32::NAN`, `opt_ne_self` returns `true` and `tup_eq_self`, `arr_eq_self` and
//@ accept-means: `ref_eq_self` return `false`; an accept claims the opposite of each.
//@ fixed-by: D-215
//@ teeth: ACCEPTED on the campaign tip before D-215 (each of the four functions verified); each is
//@ teeth: `unknown` under D-215.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(!result)]
pub fn opt_ne_self(x: f32) -> bool {
    let o = Some(x);
    o != o
}

#[ensures(result)]
pub fn tup_eq_self(x: f32, y: f32) -> bool {
    let p = (x, y);
    p == p
}

#[ensures(result)]
pub fn arr_eq_self(x: f32) -> bool {
    let a = [x, x];
    a == a
}

#[ensures(result)]
pub fn ref_eq_self(x: f32) -> bool {
    let r = &x;
    r == r
}
