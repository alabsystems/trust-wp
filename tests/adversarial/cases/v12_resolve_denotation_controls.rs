//@ expect: verify
//@ mechanism: controls for the v12 cases: `resolve` stays the by-value `true` of a variable annotated
//@ mechanism: at a sort certainly holding no borrow (an integer parameter or result, a shared
//@ mechanism: reference to one), and a borrow whose final value the lane names
//@ mechanism: keeps its `*x == ^x` reading; the closure postcondition's reborrow contract keeps its
//@ mechanism: reading of the returned borrow.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(|r: &mut i32| ^x == ^r && *r == *x)]
pub fn give(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(resolve(v))]
pub fn by_value(v: i32) {}

#[ensures(resolve(result))]
pub fn by_value_result(v: i32) -> i32 {
    v
}

#[ensures(resolve(r))]
pub fn shared(r: &i32) {}

#[ensures(resolve(x))]
pub fn untouched(x: &mut i32) {}

#[requires(*x < 100i32)]
#[ensures(resolve(y) && ^x == *x + 1i32)]
pub fn untouched_beside_inc(x: &mut i32, y: &mut i32) {
    *x += 1;
}
