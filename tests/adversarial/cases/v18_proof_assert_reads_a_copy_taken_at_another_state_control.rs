//@ expect: verify
//@ mechanism: control for v18/v19 (D-185): a `proof_assert!` after whole-pointee stores through the
//@ mechanism: `&mut` itself reads the stored value, a copy taken before a write reads the entry value
//@ mechanism: the precondition fixes, a copy taken between two stores reads the first, an assertion
//@ mechanism: before any write reads the entry value, and a local written through a borrow of it
//@ mechanism: reads the written value, and a store after a call reads the stored value.
//@ accept-means: n/a (control)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): every function verifies with
//@ teeth: D-185; on 67fd4ea7 t1 and t3 were unknown (vacuous: the copy and the stores shared
//@ teeth: `x_current`), the rest verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

#[requires(*x != 5i32)]
pub fn z10(x: &mut i32) {
    let v = *x;
    *x = 5i32;
    proof_assert!(v != *x);
}

#[requires(*x == 0i32)]
pub fn c1(x: &mut i32) {
    *x = 5i32;
    proof_assert!(*x == 5i32);
}

#[requires(*x == 0i32)]
pub fn c3(x: &mut i32) {
    let v = *x;
    *x = 5i32;
    proof_assert!(v == 0i32);
}

#[requires(*x == 0i32)]
pub fn c4(x: &mut i32) {
    proof_assert!(*x == 0i32);
    *x = 5i32;
}

#[requires(*x.m == 0i32)]
pub fn c5(x: &mut M<'_>) {
    proof_assert!(*x.m == 0i32);
    *x.m = 5i32;
}

#[requires(*x == 0i32)]
pub fn t1(x: &mut i32) {
    *x = 5i32;
    let v = *x;
    *x = 7i32;
    proof_assert!(v == 5i32 && *x == 7i32);
}

#[requires(*x == 0i32)]
pub fn t3(x: &mut i32) {
    let v = *x + 1i32;
    *x = 5i32;
    proof_assert!(v == 1i32);
}

#[requires(true)]
pub fn t5() {
    let mut c = 0i32;
    {
        let r = &mut c;
        *r = 5i32;
    }
    proof_assert!(c == 5i32);
}

#[requires(*x.m == 0i32)]
pub fn t6(x: &mut M<'_>) {
    proof_assert!(*x.m == 0i32);
}

#[requires(*x == 0i32)]
pub fn t8(x: &mut i32) {
    let v = *x;
    *x = 5i32;
    proof_assert!(v == 0i32 && *x == 5i32);
}

#[ensures(^x == 5i32)]
pub fn set5(x: &mut i32) {
    *x = 5i32;
}

#[requires(true)]
pub fn t9(x: &mut i32) {
    set5(x);
    *x = 7i32;
    proof_assert!(*x == 7i32);
}
