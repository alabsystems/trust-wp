// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A closure's parameters are read as a function's are. The alias
//! resolution and the refusals of D-100 returned early for a closure, so a
//! binder of a closure's `&mut` parameter read under `old(..)` hid the
//! parameter from the dialect rule, and `*x` of a closure's `x: i32` was read
//! as `x`: each false clause verified.

#![feature(stmt_expr_attributes, proc_macro_hygiene)]
#![allow(unused)]

use trust_wp::prelude::*;

// FALSE: `q` is `p`, named inside `old`, so `q@` outside it is entry + 1.
pub fn let_alias() {
    let c = #[requires((*p)@ < 100)]
    #[ensures({ let q = p; old(q@) == q@ })]
    |p: &mut u32| {
        *p += 1;
    };
    let mut z = 1u32;
    c(&mut z);
}

// FALSE.
pub fn match_alias() {
    let c = #[requires((*p)@ < 100)]
    #[ensures(match p { q => old(q@) == q@ })]
    |p: &mut u32| {
        *p += 1;
    };
    let mut z = 1u32;
    c(&mut z);
}

// FALSE.
pub fn if_let_alias() {
    let c = #[requires(*p < 100i32)]
    #[ensures(if let q = p { old(*q) == *q } else { true })]
    |p: &mut i32| {
        *p += 1;
    };
    let mut z = 1i32;
    c(&mut z);
}

// No reading: `x` is no reference. The chained comparison keeps the clause
// from the Rust type-check.
pub fn deref_of_a_value() {
    let c = #[ensures(*x == result && 0 < 1 < 2)]
    |x: i32| x;
    let _ = c(3);
}

// No placement: `t.0` holds `p` other than by its name.
pub fn unplaced() {
    let c = #[requires(*p < 100i32)]
    #[ensures({ let t = (p, 0); *t.0 == old(*p) })]
    |p: &mut i32| {
        *p += 1;
    };
    let mut z = 1i32;
    c(&mut z);
}

fn main() {}
