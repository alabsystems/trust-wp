//@ expect: reject
//@ mechanism: a borrow of a `&mut` parameter's referent, or of a local, held by a tuple or struct
//@ mechanism: (built around it, or STORED into an existing holder's field as in D-128, the holder made
//@ mechanism: by a call or not), written through the holder (directly, or by a callee handed the
//@ mechanism: holder by `&mut` or by value), then read by a `proof_assert!`. D-127 item 5's staleness reached postconditions,
//@ mechanism: returned values and call preconditions, but the proof_assert lane read the place at its
//@ mechanism: value from before the write; and a borrow stored into a call-made holder's field did not
//@ mechanism: make it a holder, so a callee handed it was no write (D-129).
//@ accept-means: an assertion about a place's value after a write through a holder is credited
//@ accept-means: against the value the place had before the write.
//@ WHY THE CONTRACT IS FALSE: each body writes 5 into the place the assertion reads (`*x`, or `c`);
//@ WHY THE CONTRACT IS FALSE: executed natively, each asserted condition is false.
//@ fixed-by: D-129 (a proof_assert reading a local a holder of its borrow may have written is refused)
//@ refused-with: proof_assert in creusot_test::param_aggregate error: stale read refused
//@ also-verified: set5_tuple, set5, write_first
//@ teeth: MEASURED (debug driver, ay 57a37e51): on 2c859203 all six assertions were VERIFIED and
//@ teeth: param_aggregate, param_field_store and param_struct_store were credited: the crate was
//@ teeth: ACCEPTED. With D-129 each assertion is refused as a stale read, and those three functions are
//@ teeth: unknown; local_call_made_holder is refused only because a borrow stored into a field of a
//@ teeth: call-made value now makes it a holder. moved_holder's assertion was VERIFIED on 2c859203
//@ teeth: too (a `u32` spelling was unknown there with ay_result=unsat, the strict proof-authority gate
//@ teeth: alone), and is refused with D-129.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub fn make<'a>(r: &'a mut i32) -> M<'a> {
    M { m: r }
}

pub fn set5(h: &mut M<'_>) {
    *h.m = 5i32;
}

pub fn set5_tuple(h: &mut (&mut i32, i32)) {
    *h.0 = 5i32;
}

#[requires(*x != 5i32)]
pub fn param_aggregate(x: &mut i32) {
    let t = (&mut *x, 0i32);
    *t.0 = 5i32;
    proof_assert!(*x != 5i32);
}

#[requires(*x != 5i32)]
pub fn param_field_store(x: &mut i32) {
    let mut b = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = &mut *x;
    *t.0 = 5i32;
    proof_assert!(*x != 5i32);
}

#[requires(*x != 5i32)]
pub fn param_struct_store(x: &mut i32) {
    let mut b = 0i32;
    let mut m = M { m: &mut b };
    m.m = &mut *x;
    *m.m = 5i32;
    proof_assert!(*x != 5i32);
}

pub fn local_field_store() {
    let mut b = 0i32;
    let mut c = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = &mut c;
    *t.0 = 5i32;
    proof_assert!(c == 0i32);
}

pub fn local_field_store_callee() {
    let mut b = 0i32;
    let mut c = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = &mut c;
    set5_tuple(&mut t);
    proof_assert!(c == 0i32);
}

#[ensures(true)]
pub fn write_first(x: (&mut i32, &mut i32)) {
    *x.0 = 5i32;
}

pub fn moved_holder() {
    let mut a = 0i32;
    let mut b = 0i32;
    write_first((&mut a, &mut b));
    proof_assert!(a == 0i32);
}

pub fn local_call_made_holder() {
    let mut b = 0i32;
    let mut c = 0i32;
    let mut m = make(&mut b);
    m.m = &mut c;
    set5(&mut m);
    proof_assert!(c == 0i32);
}
