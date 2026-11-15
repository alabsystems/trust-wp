//@ expect: verify
//@ mechanism: control for r31_macro_mut_ident_binding_hygiene.rs (D-239): the same macros, with
//@ mechanism: true assertions about the binding the caller's name denotes after each macro call
//@ mechanism: (the macro's pattern binds the caller's identifier, so it is that binding): hm4 and
//@ mechanism: hc2..hc11 assert it (hc8, the tuple pattern, is the _tuple_control twin), hc3
//@ mechanism: states a true invariant over it, and hc13 keeps a macro's own hygienic `let mut x`
//@ mechanism: apart from the caller's parameter.
//@ accept-means: n/a (control) - every assertion holds.
//@ teeth: MEASURED: on 62994450 (D-238) every function but hc13 FAILED (hc3 vacuous); all
//@ teeth: verify with D-239.
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

macro_rules! own_mut_x {
    () => {
        let mut x = 7i32;
        x += 0;
        let _ = x;
    };
}

#[requires(x@ == 5)]
pub fn hm4(x: i32) {
    bind_mut!(x);
    proof_assert!(x@ == 0);
}

#[requires(x@ == 5)]
pub fn hc2(x: i32) {
    bind_ref!(x);
    proof_assert!(*x == 0i32);
}

#[requires(x@ == 5)]
#[ensures(true)]
pub fn hc3(x: i32) {
    bind_mut!(x);
    let mut i = 0i32;
    #[invariant(x@ == 0)]
    while i < 3 {
        i += 1;
    }
}

#[requires(x@ == 5)]
pub fn hc5(x: i32) {
    bind_ref_mut!(x);
    proof_assert!(*x == 0i32);
}

pub fn hc6() {
    let x = 5i32;
    bind_mut!(x);
    proof_assert!(x@ == 0);
}

#[requires(x@ == 5)]
pub fn hc9(x: i32) {
    bind_struct_mut!(x);
    proof_assert!(x@ == 0);
}

#[requires(x@ == 5)]
pub fn hc10(x: i32) {
    bind_at!(x);
    proof_assert!(x@ == 0);
}

#[requires(x@ == 5)]
pub fn hc11(x: i32) {
    bind_mut_outer!(x);
    proof_assert!(x@ == 0);
}

#[requires(x@ == 5)]
pub fn hc13(x: i32) {
    own_mut_x!();
    proof_assert!(x@ == 5);
}
