//@ expect: reject
//@ mechanism: the trait twin of v8_callsite_lent_into_raw_pointer: the impl's lane read the
//@ mechanism: pre-Creusot `*p` at entry because `mut_borrow::lent` counts the `*mut i32` it
//@ mechanism: returns, so it proved `entry == entry` (and the trait's clause through it); a call,
//@ mechanism: generic or concrete, saw no region in `*mut i32` and read `*p` as `^p`.
//@ accept-means: a caller is credited with a reading of a callee clause that no lane proved, and
//@ accept-means: the whole crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `leak2` stores 5 through the borrow of `x`, so `^x` is 5 and the
//@ WHY THE CONTRACT IS FALSE: precondition makes the entry `*x` something else; `leak2`'s own
//@ WHY THE CONTRACT IS FALSE: `*p == old(*p)` is false of the same store.
//@ fixed-by: D-102
//@ teeth: MEASURED on cbadb52d (debug driver): `<U as Leak2>::leak2 verified`, `concrete_caller
//@ teeth: verified`, `generic_caller verified`, exit 0; d454c1e1: leak2 verified, callers unknown.
//@ teeth: On the D-102 tree: leak2 refused, callers unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Leak2 {
    #[ensures(*p == old(*p))]
    fn leak2(&self, p: &mut i32) -> *mut i32;
}

pub struct U;

impl Leak2 for U {
    #[ensures(*p == old(*p))]
    fn leak2(&self, p: &mut i32) -> *mut i32 {
        *p = 5;
        p as *mut i32
    }
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn concrete_caller(x: &mut i32) {
    let _ = U.leak2(x);
}

#[ensures(^x == *x)]
pub fn generic_caller<T: Leak2>(t: &T, x: &mut i32) {
    let _ = t.leak2(x);
}
