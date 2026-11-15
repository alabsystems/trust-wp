//@ expect: reject
//@ mechanism: macro hygiene read from a binding PATTERN's span (D-239). A `macro_rules!` arm
//@ mechanism: `let mut $n = ..` (or `ref $n`, `ref mut $n`, `($n, _)`, `S { f: mut $n }`,
//@ mechanism: `$n @ _`) binds the CALLER's identifier: the name has the caller's hygiene, only
//@ mechanism: the `mut`/`ref`/`@` tokens have the macro's. D-238 took a binding's hygiene from
//@ mechanism: its MIR debug-info span, which is the pattern's (`mut x`) and so the macro's, and
//@ mechanism: then discarded the real binding as foreign: the caller's later text resolved to
//@ mechanism: the parameter (or an earlier local) the macro's binding hides.
//@ accept-means: an assertion, invariant or lemma call is read about a binding the caller's name
//@ accept-means: does not denote at that point.
//@ WHY THE CONTRACT IS FALSE: every macro binds the caller's `x` to 0 (or a reference to 0), so
//@ WHY THE CONTRACT IS FALSE: `x@ == 5` (`*x == 5i32`) is false at the assertion; hm3: the invariant
//@ WHY THE CONTRACT IS FALSE: x@ == 5 fails at entry; hm7: the lemma's precondition fails.
//@ also-verified: creusot_test::lemma_is_five
//@ fixed-by: D-239
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): on 62994450 (D-238) every
//@ teeth: function and assertion VERIFIED (hm1..hm12); with D-239 each assertion is FAILED (hm3
//@ teeth: is vacuous: its invariant's initialization is refuted).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Pt {
    pub v: i32,
    pub w: i32,
}

macro_rules! bind_mut {
    ($n:ident) => {
        let mut $n = 0i32;
        $n += 0;
    };
}

macro_rules! bind_ref {
    ($n:ident) => {
        let ref $n = 0i32;
    };
}

macro_rules! bind_ref_mut {
    ($n:ident) => {
        let ref mut $n = 0i32;
        *$n += 0;
    };
}

macro_rules! bind_tuple_mut {
    ($n:ident) => {
        let (mut $n, _) = (0i32, 1i32);
        $n += 0;
    };
}

macro_rules! bind_struct_mut {
    ($n:ident) => {
        let Pt { v: mut $n, .. } = Pt { v: 0, w: 1 };
        $n += 0;
    };
}

macro_rules! bind_at {
    ($n:ident) => {
        let $n @ _ = 0i32;
    };
}

macro_rules! bind_mut_inner {
    ($m:ident) => {
        let mut $m = 0i32;
        $m += 0;
    };
}

macro_rules! bind_mut_outer {
    ($n:ident) => {
        bind_mut_inner!($n);
    };
}

#[logic]
#[requires(a@ == 5)]
#[ensures(a@ == 5)]
pub fn lemma_is_five(a: i32) {}

#[requires(x@ == 5)]
pub fn hm1(x: i32) {
    bind_mut!(x);
    proof_assert!(x@ == 5);
}

#[requires(x@ == 5)]
pub fn hm2(x: i32) {
    bind_ref!(x);
    proof_assert!(*x == 5i32);
}

#[requires(x@ == 5)]
#[ensures(true)]
pub fn hm3(x: i32) {
    bind_mut!(x);
    let mut i = 0i32;
    #[invariant(x@ == 5)]
    while i < 3 {
        i += 1;
    }
}

#[requires(x@ == 5)]
pub fn hm5(x: i32) {
    bind_ref_mut!(x);
    proof_assert!(*x == 5i32);
}

pub fn hm6() {
    let x = 5i32;
    bind_mut!(x);
    proof_assert!(x@ == 5);
}

#[requires(x@ == 5)]
pub fn hm7(x: i32) {
    bind_mut!(x);
    proof_assert! { lemma_is_five(x); x@ == 5 };
}

#[requires(x@ == 5)]
pub fn hm8(x: i32) {
    bind_tuple_mut!(x);
    proof_assert!(x@ == 5);
}

#[requires(x@ == 5)]
pub fn hm9(x: i32) {
    bind_struct_mut!(x);
    proof_assert!(x@ == 5);
}

#[requires(x@ == 5)]
pub fn hm10(x: i32) {
    bind_at!(x);
    proof_assert!(x@ == 5);
}

#[requires(x@ == 5)]
pub fn hm11(x: i32) {
    bind_mut_outer!(x);
    proof_assert!(x@ == 5);
}

pub fn hm12() {
    let x = 5i32;
    {
        bind_mut!(x);
        proof_assert!(x@ == 5);
    }
}
