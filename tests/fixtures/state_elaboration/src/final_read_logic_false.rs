// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A logic function reads its `&mut` parameter as one value, so a final read
//! inside it (`^q`) was the current one: `unchanged(p)` (`^q == *q`) held of
//! every `p`. Every contract below is false except `keep`'s and `inc_beside`'s.

#![allow(unused)]

use std::cell::Cell;

use trust_wp::prelude::*;

#[logic(open, prophetic)]
pub fn unchanged(q: &mut i32) -> bool {
    pearlite! { ^q == *q }
}

#[logic(open, prophetic)]
pub fn flipped(q: &mut i32) -> bool {
    pearlite! { *q == ^q }
}

#[logic(open, prophetic)]
pub fn cell_unchanged(q: &mut Cell<i32>) -> bool {
    pearlite! { ^q == *q }
}

#[logic(open)]
pub fn succ(x: i32) -> Int {
    pearlite! { x@ + 1 }
}

// FALSE: stores 5 under `*p != 5`.
#[requires(*p != 5i32)]
#[ensures(unchanged(p))]
pub fn set5(p: &mut i32) {
    *p = 5;
}

// FALSE: stores 5 under `*p != 5`.
#[requires(*p != 5i32)]
#[ensures(flipped(p))]
pub fn set5_flipped(p: &mut i32) {
    *p = 5;
}

// FALSE: `slot`'s holder decides what `p` is left with.
#[ensures(unchanged(p))]
pub fn stash_logic<'a>(p: &'a mut i32, slot: &mut Option<&'a mut i32>) {
    *slot = Some(p);
}

// FALSE: writes 5 through the slot under `*x != 5`.
#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_logic_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    stash_logic(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

// FALSE: the cell is left 5.
#[ensures(cell_unchanged(x))]
pub fn cell_set(x: &mut Cell<i32>) {
    x.set(5);
}

// TRUE.
#[ensures(^v == *v)]
pub fn keep(v: &mut i32, p: &mut i32) {
    *p = 7;
}

// FALSE: the callee stores 7 under `*p != 7`.
#[requires(*p != 7i32)]
#[ensures(unchanged(p))]
pub fn keep_logic_caller(v: &mut i32, p: &mut i32) {
    keep(v, &mut *p)
}

// TRUE: a logic function reading no final value keeps its reading.
#[requires(*p < 100i32)]
#[ensures((^p)@ == succ(*p))]
pub fn inc_beside(p: &mut i32) {
    *p += 1;
}

fn main() {}
