// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A callee's postcondition in the pre-Creusot dialect (it names a `&mut`
//! parameter inside `old(..)`, so a bare `*p`, `p@` or field of `p` is the
//! value `p` is left with) is proved by the callee's lane in that dialect.
//! The call re-read the text with `*p` the value at the call and `old(e)` the
//! CALLER's entry state, so each caller below learned a false premise about
//! its entry values and verified a false contract.

#![allow(unused)]

use trust_wp::prelude::*;

#[ensures(*a == old(*b) && *b == old(*a))]
pub fn swap(a: &mut i32, b: &mut i32) {
    let t = *a;
    *a = *b;
    *b = t;
}

// FALSE: with *x = 1, *y = 2 at entry.
#[ensures(*x == *y)]
pub fn swap_caller(x: &mut i32, y: &mut i32) {
    swap(x, y)
}

#[ensures(*p == v && result == old(*p))]
pub fn replace(p: &mut u32, v: u32) -> u32 {
    let o = *p;
    *p = v;
    o
}

// FALSE: with *x = 1 at entry, `replace(x, 7)` returns 1.
#[ensures(result == 7u32)]
pub fn replace_caller(x: &mut u32) -> u32 {
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

// FALSE: with c.v = 1 at entry, `c.put(3)` returns 1.
#[ensures(result == 3i32)]
pub fn put_caller(c: &mut Cell) -> i32 {
    c.put(3)
}

#[ensures(*p == v && old(*p) - old(*p) == 0i32)]
pub fn set(p: &mut i32, v: i32) {
    *p = v;
}

// FALSE: the entry value of `*q` is arbitrary.
#[ensures(*q == 9i32)]
pub fn set_caller(q: &mut i32) {
    set(q, 9)
}

#[requires(*v < 100i32)]
#[ensures(*v == old(*v) + 1i32)]
pub fn inc(v: &mut i32) {
    *v += 1;
}

// FALSE: `x` is left one above its entry value.
#[requires(*x < 50i32)]
#[ensures(^x == *x)]
pub fn inc_caller(x: &mut i32) {
    inc(x)
}

// FALSE: `y` is 6 after the call.
#[ensures(result == 5i32)]
pub fn local_inc_false() -> i32 {
    let mut y = 5i32;
    inc(&mut y);
    y
}

#[ensures(|r| r == 5i32)]
pub fn five() -> i32 {
    5
}

// FALSE.
#[ensures(result == 6i32)]
pub fn five_caller() -> i32 {
    five()
}

fn main() {}
