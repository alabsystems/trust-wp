// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The true readings of the callees in `call_old_dialect_false`: a caller is
//! credited with the post-state the callee's own lane proved. Each was
//! unknown, vacuous or FAILED while the call read `*p` at the call and `old`
//! at the caller's entry: `inc`'s `*v == old(*v) + 1` became `x == x + 1`, and
//! a closure-style `|r| r == 5` was applied as an unapplied closure.

#![allow(unused)]

use trust_wp::prelude::*;

#[ensures(*a == old(*b) && *b == old(*a))]
pub fn swap(a: &mut i32, b: &mut i32) {
    let t = *a;
    *a = *b;
    *b = t;
}

#[ensures(^x == *y && ^y == *x)]
pub fn swap_caller_control(x: &mut i32, y: &mut i32) {
    swap(x, y)
}

#[ensures(*p == v && result == old(*p))]
pub fn replace(p: &mut u32, v: u32) -> u32 {
    let o = *p;
    *p = v;
    o
}

#[ensures(result == *x && ^x == 7u32)]
pub fn replace_caller_control(x: &mut u32) -> u32 {
    replace(x, 7)
}

pub struct Cell {
    pub v: i32,
}

impl Cell {
    #[ensures(self.v == x && result == old(self.v))]
    pub fn put(&mut self, x: i32) -> i32 {
        let o = self.v;
        self.v = x;
        o
    }
}

#[ensures(result == c.v && (^c).v == 3i32)]
pub fn put_caller_control(c: &mut Cell) -> i32 {
    c.put(3)
}

#[ensures(*p == v && old(*p) - old(*p) == 0i32)]
pub fn set(p: &mut i32, v: i32) {
    *p = v;
}

#[ensures(^q == 9i32)]
pub fn set_caller_control(q: &mut i32) {
    set(q, 9)
}

#[requires(*v < 100i32)]
#[ensures(*v == old(*v) + 1i32)]
pub fn inc(v: &mut i32) {
    *v += 1;
}

#[requires(*x < 50i32)]
#[ensures(^x == *x + 1i32)]
pub fn inc_caller_control(x: &mut i32) {
    inc(x)
}

#[ensures(result == 6i32)]
pub fn local_inc_true() -> i32 {
    let mut y = 5i32;
    inc(&mut y);
    y
}

#[requires(*p < 100u32)]
#[ensures(p@ == old(p@) + 1)]
pub fn inc_view(p: &mut u32) {
    *p += 1;
}

#[ensures(result == 6u32)]
pub fn local_inc_view_true() -> u32 {
    let mut y = 5u32;
    inc_view(&mut y);
    y
}

#[ensures(|r| r == 5i32)]
pub fn five() -> i32 {
    5
}

#[ensures(result == 5i32)]
pub fn five_caller_control() -> i32 {
    five()
}

#[ensures(|(a, b)| a == 1i32 && b == 2i32)]
pub fn pair() -> (i32, i32) {
    (1, 2)
}

#[ensures(result == 1i32)]
pub fn pair_caller_control() -> i32 {
    pair().0
}

fn main() {}
