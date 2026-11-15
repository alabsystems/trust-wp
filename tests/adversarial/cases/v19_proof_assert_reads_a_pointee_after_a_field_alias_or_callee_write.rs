//@ expect: reject
//@ mechanism: a `proof_assert!` reads a `&mut` parameter's pointee after a write the lane does not
//@ mechanism: record as its current value, and is credited from a stale one: a field of the pointee
//@ mechanism: stored (`x.f = 5`, q7: read at the entry, so the precondition `x.f == 0` proves it),
//@ mechanism: a held borrow redirected to another borrow (`x.m = y`, r13: `*x.m` read at the entry
//@ mechanism: borrow's pointee), an uncontracted callee after a contracted one (`set5(x);
//@ mechanism: opaque(x)`, q1: read as `set5`'s postcondition, the second call not advancing the
//@ mechanism: borrow), and a store before a contracted callee (`*x = 7; set5(x)`, q5: read as the
//@ mechanism: store, the call not reaching the recorded pointee).
//@ accept-means: a `proof_assert!` about a pointee is credited from a value an earlier or a missing
//@ accept-means: write left, not from the value the pointee holds at the assertion.
//@ WHY THE CONTRACT IS FALSE: q7: `x.f` is 5 at the assertion, not 0; r13: `*x.m` is `*y`, which
//@ WHY THE CONTRACT IS FALSE: nothing fixes (`r13(&mut M { m: &mut 0 }, &mut 1)` asserts `1 == 0`);
//@ WHY THE CONTRACT IS FALSE: q1: `opaque` leaves 7; q5: `set5` leaves 5; q2: the store after `set5` leaves 7.
//@ fixed-by: D-185 (an assertion reading memory a write may have changed before it is refused
//@ fixed-by: unless every such write is a whole-pointee store the walk records)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on 67fd4ea7 the proof_asserts of q7, r13, q1 and q5 were VERIFIED (q7 and r13 with their
//@ teeth: functions); with D-185 each is refused as a stale read. q2 (the store overwrites the
//@ teeth: callee's write, which D-185 reads as the store) was inconclusive on 67fd4ea7.
//@ also-verified: set5
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub struct S {
    pub f: i32,
    pub g: i32,
}

#[ensures(^x == 5i32)]
pub fn set5(x: &mut i32) {
    *x = 5i32;
}

pub fn opaque(x: &mut i32) {
    *x = 7i32;
}

#[requires(x.f == 0i32)]
pub fn q7(x: &mut S) {
    x.f = 5i32;
    proof_assert!(x.f == 0i32);
}

#[requires(*x.m == 0i32)]
pub fn r13<'a>(x: &mut M<'a>, y: &'a mut i32) {
    x.m = y;
    proof_assert!(*x.m == 0i32);
}

pub fn q1(x: &mut i32) {
    set5(x);
    opaque(x);
    proof_assert!(*x == 5i32);
}

pub fn q5(x: &mut i32) {
    *x = 7i32;
    set5(x);
    proof_assert!(*x == 7i32);
}

pub fn q2(x: &mut i32) {
    set5(x);
    *x = 7i32;
    proof_assert!(*x == 5i32);
}
