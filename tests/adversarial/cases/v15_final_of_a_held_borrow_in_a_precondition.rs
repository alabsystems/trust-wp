//@ expect: reject
//@ mechanism: a PRECONDITION reading the final value of a borrow a field, element or referent of a
//@ mechanism: reference parameter holds (`^x.m`, `^(x.m)`, `^*x`, `^x[0]`, `^s.m` of a shared
//@ mechanism: `s`). The contract lane's held-borrow guard (D-127 item 3, D-129 item 2) ran on
//@ mechanism: postconditions only; the encoder read the precondition's `^x.m` by the reborrow rule
//@ mechanism: as `(^x).m`, the field the OUTER borrow is left with, which the body's `*x.m = 5`
//@ mechanism: decides, so `k == 5` followed from `^x.m == k`.
//@ accept-means: a precondition about a held borrow's final value is read as the body's write, and a
//@ accept-means: postcondition the caller can falsify is credited.
//@ WHY THE CONTRACT IS FALSE: `let mut c = 0; let mut m = M { m: &mut c }; req_field_int(&mut m, 0);
//@ WHY THE CONTRACT IS FALSE: *m.m = 0;` ends the inner borrow at 0, so `^x.m == k` holds with
//@ WHY THE CONTRACT IS FALSE: k == 0 while `ensures(k == 5)` fails.
//@ fixed-by: D-183 (a final read of a value reached through a reference parameter by a projection is
//@ fixed-by: refused by the parameter's type in every clause: precondition, postcondition,
//@ fixed-by: proof_assert, loop invariant, and a callee's precondition at every call)
//@ refused-with: final value of a value held through the
//@ teeth: MEASURED (debug driver, ay 561e68c7c): on f214082f req_field_int, req_field_int_paren and
//@ teeth: req_field_ref were VERIFIED; req_deref, req_index and req_shared unknown, req_struct2
//@ teeth: refused in the encoder; with D-183 all seven are refused at placement.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub struct S<'a> {
    pub m: &'a mut i32,
    pub v: i32,
}

#[requires(^x.m == k)]
#[ensures(k == 5i32)]
pub fn req_field_int(x: &mut M<'_>, k: i32) {
    *x.m = 5i32;
}

#[requires(^(x.m) == k)]
#[ensures(k == 5i32)]
pub fn req_field_int_paren(x: &mut M<'_>, k: i32) {
    *x.m = 5i32;
}

#[requires(^x.m == *y)]
#[ensures(*y == 5i32)]
pub fn req_field_ref(x: &mut M<'_>, y: &i32) {
    *x.m = 5i32;
}

#[requires(^*x == k)]
#[ensures(k == 5i32)]
pub fn req_deref(x: &mut &mut i32, k: i32) {
    **x = 5i32;
}

#[requires(^x[0] == k)]
#[ensures(k == 5i32)]
pub fn req_index(x: &mut [&mut i32; 1], k: i32) {
    *x[0] = 5i32;
}

#[requires(^x.m == k)]
#[ensures(k == 5i32)]
pub fn req_struct2(x: &mut S<'_>, k: i32) {
    *x.m = 5i32;
}

#[requires(^s.m == k)]
#[ensures(k == *s.m)]
pub fn req_shared(s: &M<'_>, k: i32) {}
