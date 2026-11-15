//@ expect: reject
//@ mechanism: a `proof_assert!` that reads the pointee of a borrow a HOLDER owns (`*x.m` of
//@ mechanism: `x: &mut M { m: &mut i32 }`, a tuple, a tuple struct, a nested or generic holder,
//@ mechanism: a by-value holder, `&mut self`, a `Box` field) AFTER the body wrote through it is
//@ mechanism: read at the ENTRY state: the write contributes no premise, the goal `*x.0 == 0` is
//@ mechanism: syntactically the precondition, and the ExactPreparedPremise slice discharges it
//@ mechanism: without the vacuity/solver lane. The plain `x: &mut i32` spelling k14 was refused as a
//@ mechanism: vacuous proof (the entry and the current pointee shared `x_current`). No copy is
//@ mechanism: involved, which separates it from v18.
//@ accept-means: a `proof_assert!` about a held borrow's pointee is credited from the entry value
//@ accept-means: although the body wrote a different value through that borrow before it.
//@ WHY THE CONTRACT IS FALSE: every precondition fixes the pointee at 0 (or != 5) and the body
//@ WHY THE CONTRACT IS FALSE: writes 5 through the held borrow before the assertion, so at the
//@ WHY THE CONTRACT IS FALSE: assertion the pointee is 5: `*x.m == 0` / `*x.m != 5` is false.
//@ fixed-by: D-185 (an assertion reading memory a write may have changed before it is refused
//@ fixed-by: unless the write is a whole-pointee store the walk records, which it then reads)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on 67fd4ea7 k1..k12 and M::k13 were VERIFIED with their proof_asserts credited, k14
//@ teeth: unknown (vacuous); with D-185 k1..k13 are refused as stale reads and k14 is FAILED.
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

pub struct O<'a> {
    pub i: M<'a>,
}

pub struct G<'a, T> {
    pub m: &'a mut T,
}

pub struct BX {
    pub m: Box<i32>,
}

#[requires(*x.m == 0i32)]
pub fn k1(x: &mut M<'_>) {
    *x.m = 5i32;
    proof_assert!(*x.m == 0i32);
}

#[requires(*x.m != 5i32)]
pub fn k2(x: &mut M<'_>) {
    *x.m = 5i32;
    proof_assert!(*x.m != 5i32);
}

#[requires(*x.m == 0i32)]
pub fn k3(x: &mut S<'_>) {
    *x.m = 5i32;
    proof_assert!(*x.m == 0i32);
}

#[requires(*x.0 == 0i32)]
pub fn k4(x: &mut N<'_>) {
    *x.0 = 5i32;
    proof_assert!(*x.0 == 0i32);
}

#[requires(*x.0 == 0i32)]
pub fn k5(x: &mut (&mut i32,)) {
    *x.0 = 5i32;
    proof_assert!(*x.0 == 0i32);
}

#[requires(*x.m == 0i32)]
pub fn k6(x: M<'_>) {
    *x.m = 5i32;
    proof_assert!(*x.m == 0i32);
}

#[requires(*x.i.m == 0i32)]
pub fn k7(x: &mut O<'_>) {
    *x.i.m = 5i32;
    proof_assert!(*x.i.m == 0i32);
}

#[requires(*x.m == 0i32)]
pub fn k8(x: &mut G<'_, i32>) {
    *x.m = 5i32;
    proof_assert!(*x.m == 0i32);
}

#[requires(*x.m == 0i32)]
pub fn k9(x: &mut BX) {
    *x.m = 5i32;
    proof_assert!(*x.m == 0i32);
}

#[requires(*x.m == 0i32)]
pub fn k10(x: &mut M<'_>) {
    let r = &mut *x.m;
    *r = 5i32;
    proof_assert!(*x.m == 0i32);
}

#[requires(*x.m == 0i32)]
pub fn k11(x: &mut M<'_>) {
    let p = &mut x.m;
    **p = 5i32;
    proof_assert!(*x.m == 0i32);
}

#[requires(*x.m == 0i32)]
pub fn k12(x: &mut M<'_>) {
    let h = &mut *x;
    *h.m = 5i32;
    proof_assert!(*x.m == 0i32);
}

impl<'a> M<'a> {
    #[requires(*self.m == 0i32)]
    pub fn k13(&mut self) {
        *self.m = 5i32;
        proof_assert!(*self.m == 0i32);
    }
}

#[requires(*x == 0i32)]
pub fn k14(x: &mut i32) {
    *x = 5i32;
    proof_assert!(*x == 0i32);
}
