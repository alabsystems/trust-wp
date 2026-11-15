//@ expect: reject
//@ mechanism: a write THROUGH a borrow that a ONE-field referent of a `&mut` parameter holds
//@ mechanism: (`*x.m = 5` of `x: &mut M { m: &mut i32 }`, `*x.0 = 5` of `x: &mut (&mut i32,)` or of
//@ mechanism: a one-field tuple struct) never reached the value the parameter is left with. The
//@ mechanism: per-field write was recorded as `x.0`, but the whole-referent reconstruction ran only
//@ mechanism: for referents of two or more fields, so `^x` kept the entry identity `^x == *x` and
//@ mechanism: every clause reading a field of `^x` (`(^x).m`, or `x.m` as the value `x` is left
//@ mechanism: with beside `old(..)`) read the ENTRY borrow, whose current is not 5.
//@ accept-means: a postcondition about the borrow a one-field holder is left with is read at the
//@ accept-means: entry value although the body wrote through it, so a false current-value claim is
//@ accept-means: credited.
//@ WHY THE CONTRACT IS FALSE: `let mut c = 0; let mut m = M { m: &mut c }; k3(&mut m);` leaves
//@ WHY THE CONTRACT IS FALSE: `*m.m == 5` while `old(*x.m)` is 0, so `old(*x.m) == *x.m` fails;
//@ WHY THE CONTRACT IS FALSE: in Creusot's reading `*(^x).m` is 5 and `*(*x).m` is 0, so the
//@ WHY THE CONTRACT IS FALSE: `(^x).m == (*x).m` forms fail too; the tuple holders likewise.
//@ fixed-by: D-184 (the per-field reconstruction covers one-field referents, and a write through a
//@ fixed-by: borrow a `&mut` parameter's referent holds, or any per-field write that leaves `^x`
//@ fixed-by: the entry identity, takes the force off `^x`'s premise)
//@ teeth: MEASURED (debug driver, ay aba6406be, clean ae4c8f59e): on a76f9b72 k3, r1, r2, r3, r4,
//@ teeth: n1, t1 and t2 were VERIFIED; the two-field s4 and the `&mut self` m1/m3, the store q1 and
//@ teeth: the field-reborrow write q3 were unknown; with D-184 all are unknown.
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

pub struct N<'a>(pub &'a mut i32);

#[requires(*x.m != 5i32)]
#[ensures(old(*x.m) == *x.m)]
pub fn k3(x: &mut M<'_>) {
    *x.m = 5i32;
}

#[requires(*x.m != 5i32)]
#[ensures(x.m == old(x.m))]
pub fn r1(x: &mut M<'_>) {
    *x.m = 5i32;
}

#[requires(*x.m != 5i32)]
#[ensures(*x.m == *old(x.m))]
pub fn r2(x: &mut M<'_>) {
    *x.m = 5i32;
}

#[requires(*x.m != 5i32)]
#[ensures((^x).m == (*x).m)]
pub fn r3(x: &mut M<'_>) {
    *x.m = 5i32;
}

#[requires(*x.m != 5i32)]
#[ensures(*(^x).m == *(*x).m)]
pub fn r4(x: &mut M<'_>) {
    *x.m = 5i32;
}

#[requires(*x.0 != 5i32)]
#[ensures(*(^x).0 == *(*x).0)]
pub fn n1(x: &mut N<'_>) {
    *x.0 = 5i32;
}

#[requires(*x.0 != 5i32)]
#[ensures(*(^x).0 == *(*x).0)]
pub fn t1(x: &mut (&mut i32,)) {
    *x.0 = 5i32;
}

#[requires(*x.0 != 5i32)]
#[ensures(old(*x.0) == *x.0)]
pub fn t2(x: &mut (&mut i32,)) {
    *x.0 = 5i32;
}

#[requires(*x.m != 5i32)]
#[ensures(*(^x).m == *(*x).m)]
pub fn s4(x: &mut S<'_>) {
    *x.m = 5i32;
}

#[requires(*x.m != *y)]
#[ensures(*(^x).m == *(*x).m)]
pub fn q1<'a>(x: &mut M<'a>, y: &'a mut i32) {
    x.m = y;
}

#[requires(*x.m != 5i32)]
#[ensures(*(^x).m == *(*x).m)]
pub fn q3(x: &mut M<'_>) {
    let r = &mut *x.m;
    *r = 5i32;
}

impl<'a> M<'a> {
    #[requires(*self.m != 5i32)]
    #[ensures(*(^self).m == *(*self).m)]
    pub fn m1(&mut self) {
        *self.m = 5i32;
    }

    #[requires(*self.m != 5i32)]
    #[ensures(old(*self.m) == *self.m)]
    pub fn m3(&mut self) {
        *self.m = 5i32;
    }
}
