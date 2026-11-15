//@ expect: reject
//@ mechanism: a `&mut` parameter ASSIGNED into a field, element or nested field of a holder that
//@ mechanism: already exists (`t.0 = x`, `t.0 = &mut *x`, `m.m = x`, `arr[0] = x`, `arr[i] = x`,
//@ mechanism: `(t.0).0 = x`) and written through that place, directly, through a copy moved out of
//@ mechanism: it, or by a callee handed the holder. The borrow tracker followed a borrow into a
//@ mechanism: projection-less local (alias propagation) and into a place reached through a `Deref`
//@ mechanism: (D-79), but a Field or Index projection of a local was neither, so nothing charged the
//@ mechanism: escape: the parameter kept its identity resolve and its final value read as its entry
//@ mechanism: value. A holder BUILT from the borrow (`let t = (x, 0)`) was already seen.
//@ accept-means: a function that leaves `*x` at 5 is credited with `^x == *x` (or `resolve(x)`)
//@ accept-means: under `*x != 5`, and a caller is credited with `result == 3` over it although it
//@ accept-means: returns 5.
//@ WHY THE CONTRACT IS FALSE: each body lands 5 in `*x`, whose entry value is not 5; `caller`'s `a`
//@ WHY THE CONTRACT IS FALSE: is 5 after the call. Executed natively, each body leaves `*x` at 5.
//@ fixed-by: D-128 (a borrow VALUE stored into any projected place, not only one reached through a
//@ fixed-by: `Deref`, havocs the root of every tracked borrow it carries)
//@ teeth: MEASURED (debug driver): before D-128 every function here verified and the crate was
//@ teeth: ACCEPTED; D-128 leaves each false contract unknown, and withdraws `caller`'s credit because
//@ teeth: its callee no longer proves its own contract.
//@ also-verified: touch_tuple
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
    *x.0 = 5i32;
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn tuple_field_assigned(x: &mut i32) {
    let mut b = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = x;
    *t.0 = 5i32;
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn tuple_field_reborrow_assigned(x: &mut i32) {
    let mut b = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = &mut *x;
    *t.0 = 5i32;
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn struct_field_assigned(x: &mut i32) {
    let mut b = 0i32;
    let mut m = M { m: &mut b };
    m.m = x;
    *m.m = 5i32;
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn array_elem_assigned(x: &mut i32) {
    let mut b = 0i32;
    let mut arr = [&mut b];
    arr[0] = x;
    *arr[0] = 5i32;
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn array_index_assigned(x: &mut i32, i: usize) {
    let mut b = 0i32;
    let mut c = 0i32;
    let mut arr = [&mut b, &mut c];
    if i < 2 {
        arr[i] = x;
        *arr[i] = 5i32;
    }
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn nested_field_assigned(x: &mut i32) {
    let mut b = 0i32;
    let mut t = ((&mut b, 1i32), 0i32);
    (t.0).0 = x;
    *(t.0).0 = 5i32;
}

#[requires(*x != 5i32)]
#[ensures(resolve(x))]
pub fn tuple_field_assigned_resolve(x: &mut i32) {
    let mut b = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = x;
    *t.0 = 5i32;
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn field_assigned_then_callee(x: &mut i32) {
    let mut b = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = x;
    touch_tuple(&mut t);
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn field_assigned_moved_out(x: &mut i32) {
    let mut b = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = x;
    let r = t.0;
    *r = 5i32;
}

#[ensures(result == 3i32)]
pub fn caller() -> i32 {
    let mut a = 3i32;
    tuple_field_assigned(&mut a);
    a
}
