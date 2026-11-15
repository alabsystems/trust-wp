// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A callee's entry state is the call's pre-state. The call read the callee's
//! `old(e)` as the CALLER's entry state, and an argument read through a
//! reference after a store through it as the pointee's entry value, so each
//! caller below, which writes before it calls, learned a premise about its
//! own entry values and verified a false contract.

#![allow(unused)]

use trust_wp::prelude::*;

#[ensures(result == old(*p))]
pub fn get(p: &mut i32) -> i32 {
    *p
}

// FALSE: the result is 5.
#[ensures(result == *x)]
pub fn get_caller_false(x: &mut i32) -> i32 {
    *x = 5;
    get(x)
}

#[ensures(result == *p)]
pub fn get_creusot(p: &mut i32) -> i32 {
    *p
}

// FALSE: the result is 5.
#[ensures(result == *x)]
pub fn get_creusot_caller_false(x: &mut i32) -> i32 {
    *x = 5;
    get_creusot(x)
}

// FALSE: the result is `Some(3)` (a std spec, `result == old(*self)`).
#[ensures(result == *o)]
pub fn take_false(o: &mut Option<i32>) -> Option<i32> {
    *o = Some(3);
    o.take()
}

#[ensures(^a == old(*b) && ^b == old(*a))]
pub fn swap_mixed(a: &mut i32, b: &mut i32) {
    let t = *a;
    *a = *b;
    *b = t;
}

// FALSE: `y` is left 5.
#[ensures(^y == *x)]
pub fn swap_after_write_false(x: &mut i32, y: &mut i32) {
    *x = 5;
    swap_mixed(x, y)
}

#[requires(v < 100i32)]
#[ensures(result == old(v) + 1i32)]
pub fn succ(v: i32) -> i32 {
    v + 1
}

// FALSE: the result is 8.
#[requires(*x < 100i32 && *x > -100i32)]
#[ensures(result == *x + 1i32)]
pub fn succ_after_write_false(x: &mut i32) -> i32 {
    *x = 7;
    succ(*x)
}

fn main() {}
