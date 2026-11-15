//@ expect: reject
//@ mechanism: macro hygiene (D-238). A `let x` that a `macro_rules!` expansion introduces is a
//@ mechanism: hygienic binding: the caller's `x` written after the macro call is NOT it. The
//@ mechanism: D-237 resolver picked the binding an assertion names by MIR source-scope nesting
//@ mechanism: and source name alone, so the macro's binding, whose scope encloses the caller's
//@ mechanism: later statements, captured the caller's `proof_assert!(x..)`. mh1/mh5: a parameter
//@ mechanism: the macro's `let x` hides by name only; mh2: a caller local; mh4: the same inside an
//@ mechanism: inner block. mi1: a loop invariant over the caller's `x`, read at its loop header the
//@ mechanism: same way. ml1: the lemma call leading an assertion, read with it.
//@ accept-means: the assertion is read about the macro's hygienic binding, not the caller's.
//@ WHY THE CONTRACT IS FALSE: mh1: the caller's x is the parameter, 5. mh2: the caller's x is 0.
//@ WHY THE CONTRACT IS FALSE: mh4: the caller's x is 1. mh5: the caller's x is the parameter, 1.
//@ WHY THE CONTRACT IS FALSE: mi1: the invariant does not hold at entry, x is 5. ml1: x is 5, so the
//@ WHY THE CONTRACT IS FALSE: lemma's precondition fails and the assertion is false.
//@ also-verified: creusot_test::lemma_is_zero
//@ fixed-by: D-238
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): before D-238 every assertion
//@ teeth: VERIFIED and each function with it (mi1 too); with D-238 each is FAILED (mi1 vacuous).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

macro_rules! zero_x {
    () => {
        let x = 0i32;
        let _ = x;
    };
}

macro_rules! five_x {
    () => {
        let x = 5i32;
        let _ = x;
    };
}

macro_rules! bump_local {
    () => {
        let mut x = 0i32;
        x += 7;
        let _ = x;
    };
}

macro_rules! bind_x_to {
    ($e:expr) => {
        let x = $e;
        let _ = x;
    };
}

#[requires(x@ == 5)]
pub fn mh1(x: i32) {
    zero_x!();
    proof_assert!(x@ == 0);
}

pub fn mh2() {
    let x = 0i32;
    five_x!();
    proof_assert!(x@ == 5);
}

pub fn mh4() {
    let x = 1i32;
    {
        bump_local!();
        proof_assert!(x@ == 7);
    }
}

#[requires(x@ == 1)]
pub fn mh5(x: i32) {
    bind_x_to!(9i32);
    proof_assert!(x@ == 9);
}

#[requires(x@ == 5)]
#[ensures(true)]
pub fn mi1(x: i32) {
    zero_x!();
    let mut i = 0i32;
    #[invariant(x@ == 0)]
    while i < 3 {
        i += 1;
    }
}

#[logic]
#[requires(a@ == 0)]
#[ensures(a@ == 0)]
pub fn lemma_is_zero(a: i32) {}

#[requires(x@ == 5)]
pub fn ml1(x: i32) {
    zero_x!();
    proof_assert! { lemma_is_zero(x); x@ == 0 };
}
