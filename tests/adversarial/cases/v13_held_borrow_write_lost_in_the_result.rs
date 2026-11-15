//@ expect: reject
//@ mechanism: a `&mut` moved into a tuple, struct or enum and written through it, and the borrowed
//@ mechanism: local then RETURNED. tuple_held_borrow_write_lost and struct_held_borrow_write_lost gate
//@ mechanism: the same write read back by a `proof_assert!`; read through the return value into the
//@ mechanism: postcondition, the write was invisible: the result was the local's value before the
//@ mechanism: write. The store-staleness analysis joined a borrow to the local it borrows only
//@ mechanism: through reference copies, never through an aggregate that holds it, nor through a
//@ mechanism: callee handed the holder.
//@ accept-means: a function that returns 5 is credited with `result == 3`, and a call is credited
//@ accept-means: with a precondition the local it reads no longer meets.
//@ WHY THE CONTRACT IS FALSE: every write here (`*t.0 = 5`, `*m.m = 5`, `*r = 5` with `r` moved out
//@ WHY THE CONTRACT IS FALSE: of the holder, and the callees' `*x.0 = 5`, `*x.m = 5`) lands 5 in `a`,
//@ WHY THE CONTRACT IS FALSE: and each function returns `a`; `precondition_stale` hands `need_three` a
//@ WHY THE CONTRACT IS FALSE: 5.
//@ fixed-by: D-127 (an aggregate holding a borrow joins the borrowed local's alias class, and in such
//@ fixed-by: a class every call and drop handed a value of it counts as a store: the read of `a` is
//@ fixed-by: stale and fails closed)
//@ teeth: MEASURED (debug driver): before D-127 tuple_write, one_tuple_write, struct_write,
//@ teeth: moved_out, nested_tuple, reborrow_in_tuple, option_held, callee_writes_tuple,
//@ teeth: callee_writes_struct and precondition_stale verified; D-127 leaves each unknown (the stale
//@ teeth: read's fail-closed `false`) or refuted.
//@ also-verified: touch_tuple, touch_struct, need_three
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

#[ensures(true)]
pub fn touch_tuple(x: &mut (&mut i32, i32)) {
    *x.0 = 5;
}

#[ensures(true)]
pub fn touch_struct(x: &mut M<'_>) {
    *x.m = 5;
}

#[ensures(result == 3i32)]
pub fn tuple_write() -> i32 {
    let mut a = 3i32;
    let t = (&mut a, 0i32);
    *t.0 = 5;
    a
}

#[ensures(result == 3i32)]
pub fn one_tuple_write() -> i32 {
    let mut a = 3i32;
    let t = (&mut a,);
    *t.0 = 5;
    a
}

#[ensures(result == 3i32)]
pub fn struct_write() -> i32 {
    let mut a = 3i32;
    let m = M { m: &mut a };
    *m.m = 5;
    a
}

#[ensures(result == 3i32)]
pub fn moved_out() -> i32 {
    let mut a = 3i32;
    let t = (&mut a, 0i32);
    let r = t.0;
    *r = 5;
    a
}

#[ensures(result == 3i32)]
pub fn nested_tuple() -> i32 {
    let mut a = 3i32;
    let t = ((&mut a, 1i32), 0i32);
    *(t.0).0 = 5;
    a
}

#[ensures(result == 3i32)]
pub fn reborrow_in_tuple() -> i32 {
    let mut a = 3i32;
    let r = &mut a;
    let t = (&mut *r, 0i32);
    *t.0 = 5;
    a
}

#[ensures(result == 3i32)]
pub fn option_held() -> i32 {
    let mut a = 3i32;
    let o = Some(&mut a);
    if let Some(r) = o {
        *r = 5;
    }
    a
}

#[ensures(result == 3i32)]
pub fn callee_writes_tuple() -> i32 {
    let mut a = 3i32;
    let mut t = (&mut a, 0i32);
    touch_tuple(&mut t);
    a
}

#[ensures(result == 3i32)]
pub fn callee_writes_struct() -> i32 {
    let mut a = 3i32;
    let mut m = M { m: &mut a };
    touch_struct(&mut m);
    a
}

#[requires(v == 3i32)]
#[ensures(true)]
pub fn need_three(v: i32) {}

#[ensures(true)]
pub fn precondition_stale() {
    let mut a = 3i32;
    let t = (&mut a, 0i32);
    *t.0 = 5;
    need_three(a);
}
