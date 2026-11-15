//@ expect: reject
//@ mechanism: a value copied out of a `&mut` pointee (`let v = *x`, `let v = *x.m`, `let v = *x + 1`)
//@ mechanism: is read by a `proof_assert!` after a write changed the pointee. The proof_assert lane
//@ mechanism: named the entry pointee and the current one by ONE symbol (`x_current`): the copy
//@ mechanism: taken BEFORE the write was bound `v == x_current` and the write `x_current == 5`, so `v`
//@ mechanism: read the written value (f0, h0, h5, h9, d5); a copy taken AFTER a write was translated
//@ mechanism: as the entry pointee `Deref(Var x)` and then read the LAST write (r2, r14); a copy
//@ mechanism: computed from the pointee was resolved through the later `*x` binding (r1); and a
//@ mechanism: copy before a contracted callee wrote the pointee read the callee's postcondition
//@ mechanism: (d7, q6). The committed-RED proof_assert_mut_param_copy_read_after_later_write is the
//@ mechanism: one-function spelling of f0/h0.
//@ accept-means: a `proof_assert!` about a copy is credited from the value the pointee holds at
//@ accept-means: another program point than the one the copy was taken at.
//@ WHY THE CONTRACT IS FALSE: each copy holds the pointee at its own point: the entry value (which
//@ WHY THE CONTRACT IS FALSE: the preconditions keep away from 5, or leave free), or 5 where r2/r14
//@ WHY THE CONTRACT IS FALSE: copy after `*x = 5`; every assertion claims a value the copy does not
//@ WHY THE CONTRACT IS FALSE: hold (`f0(&mut 1)`: `v` is 1, `*x` is 5; `r14(&mut 0)`: `v` is 5).
//@ WHY THE CONTRACT IS FALSE: h9's second assertion, `*x == 5`, is true and declared.
//@ fixed-by: D-185 (a read through a dereference after a write takes the walk's recorded value or a
//@ fixed-by: fresh symbol; a written pointee's current-value bindings resolve into no copy and
//@ fixed-by: become no fact; an assertion reading the pointee after an untracked write is refused)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on 67fd4ea7 the proof_asserts of f0, h0, h5, h9 (both), d5, d7, r1, r2, r14 and q6
//@ teeth: were VERIFIED (f0, d5, d7, r1, r2 and r14 with their functions, d7's then withdrawn for
//@ teeth: set5t); with D-185 none of the false ones is (r2 and r14 are FAILED).
//@ also-verified: set5, set5t
//@ also-verified-assertion: creusot_test::h9
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

#[ensures(^x == 5i32)]
pub fn set5(x: &mut i32) {
    *x = 5i32;
}

#[ensures(*(^x).0 == 5i32)]
pub fn set5t(x: &mut (&mut i32,)) {
    *x.0 = 5i32;
}

#[requires(*x != 5i32)]
pub fn f0(x: &mut i32) {
    let v = *x;
    *x = 5i32;
    proof_assert!(v == *x);
}

pub fn h0(x: &mut i32) {
    let v = *x;
    *x = 5i32;
    proof_assert!(v == 5i32);
}

pub fn h5(x: &mut i32, y: i32) {
    let v = *x;
    *x = y;
    proof_assert!(v == y);
}

pub fn h9(x: &mut i32) {
    let v = *x;
    *x = 5i32;
    proof_assert!(v == 5i32);
    proof_assert!(*x == 5i32);
}

#[requires(*x.m != 5i32)]
pub fn d5(x: &mut M<'_>) {
    let v = *x.m;
    *x.m = 5i32;
    proof_assert!(v == *x.m);
}

#[requires(*x.0 != 5i32)]
pub fn d7(x: &mut (&mut i32,)) {
    let v = *x.0;
    set5t(x);
    proof_assert!(v == *x.0);
}

#[requires(*x == 0i32)]
pub fn r1(x: &mut i32) {
    let v = *x + 1i32;
    *x = 5i32;
    proof_assert!(v == 6i32);
}

#[requires(*x == 0i32)]
pub fn r2(x: &mut i32) {
    *x = 5i32;
    let v = *x;
    *x = 7i32;
    proof_assert!(v == 7i32);
}

#[requires(*x == 0i32)]
pub fn r14(x: &mut i32) {
    *x = 5i32;
    let v = *x;
    *x = 7i32;
    proof_assert!(v == 0i32);
}

pub fn q6(x: &mut i32) {
    set5(x);
    let v = *x;
    *x = 7i32;
    proof_assert!(v == 7i32);
}
