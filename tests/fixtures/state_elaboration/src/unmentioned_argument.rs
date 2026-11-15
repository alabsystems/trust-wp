// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A reborrow of a reborrow passed to a callee: the callee's clause is all a
//! caller learns of the argument's final value. The two-phase writeback of
//! the inner reborrow into the outer one fused the outer one's entry value
//! with the callee's final, so a clause silent about the argument left it
//! unchanged (`keep_caller`), and a clause that moves it made the premises
//! contradictory (`inc_caller_reborrow`).

#![allow(unused)]

use trust_wp::prelude::*;

#[ensures(^v == *v)]
pub fn keep(v: &mut i32, p: &mut i32) {
    *p = 7;
}

// FALSE: `p` is left 7.
#[requires(*p != 7i32)]
#[ensures(^p == *p)]
pub fn keep_caller(v: &mut i32, p: &mut i32) {
    keep(v, &mut *p)
}

// FALSE: `p` is left 7.
#[requires(*p != 7i32)]
#[ensures(^p == *p)]
pub fn keep_through_local(v: &mut i32, p: &mut i32) {
    let r = &mut *p;
    keep(v, r)
}

// FALSE assertion: `*p` is 7 after the call.
#[requires(*p != 7i32)]
pub fn keep_assert(v: &mut i32, p: &mut i32) {
    let before = *p;
    keep(v, &mut *p);
    proof_assert!(*p == before);
}

#[requires(*p < 100i32)]
#[ensures(^p == *p + 1i32)]
pub fn inc(p: &mut i32) {
    *p += 1;
}

// TRUE.
#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32)]
pub fn inc_caller_reborrow(x: &mut i32) {
    inc(&mut *x);
}

// TRUE: two `&mut` of one named lifetime whose referents hold no borrow lend
// nothing to each other.
#[ensures(*a == old(*b) && *b == old(*a))]
pub fn swap_old<'a>(a: &'a mut i32, b: &'a mut i32) {
    let t = *a;
    *a = *b;
    *b = t;
}

fn main() {}
