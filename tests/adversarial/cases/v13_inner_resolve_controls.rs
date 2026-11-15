//@ expect: verify
//@ mechanism: controls for the v13 cases: the outer borrow of `&mut &mut i32` resolves when the body
//@ mechanism: leaves it; `!resolve(x)` of a borrow the body writes a new value through holds; the
//@ mechanism: resolve of an untouched borrow holds; the field the outer borrow is left with is placed
//@ mechanism: (`(^x).0` of a field that is a borrow, `(^x).a` of one that is not); a chain of
//@ mechanism: dereferences of a shared reference to a value resolves (`true`; `resolve(**r)` of
//@ mechanism: `r: &&i32` was refused before D-127). The same field claims over `M { m: &mut i32 }`
//@ mechanism: (`(^x).m == (*x).m`, `*(^x).m == *(*x).m`) are left out: their evidence certification
//@ mechanism: is nondeterministic (an evidence gap in some runs), before D-127 and after.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(resolve(x))]
pub fn nested_outer(x: &mut &mut i32) {}

#[requires(*x != 5i32)]
#[ensures(!resolve(x))]
pub fn neg_var(x: &mut i32) {
    *x = 5;
}

#[ensures(resolve(x))]
pub fn untouched(x: &mut i32) {}

pub struct S {
    pub a: i32,
    pub b: i32,
}

#[ensures((^x).0 == (*x).0)]
pub fn outer_tuple_field_unchanged(x: &mut (&mut i32, i32)) {}

#[ensures((^x).a == (*x).a)]
pub fn outer_scalar_field_unchanged(x: &mut S) {}

#[ensures(resolve(*r))]
pub fn shared_deref(r: &i32) {}

#[ensures(resolve(**r))]
pub fn shared_shared_deref(r: &&i32) {}
