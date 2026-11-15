// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A `&mut` parameter whose borrow another holder may write through after
//! the call, by a write no prophecy of the function records: stored in
//! another parameter's referent (`*slot = Some(p)`, `v.push(p)`), or
//! returned as a `&Cell<i32>`. Its final value is that holder's to decide,
//! so no clause reading it is the function's to prove or its callers' to be
//! credited with: every contract below is false.

#![allow(unused)]

use std::cell::Cell;

use trust_wp::prelude::*;

#[ensures(^p == *p)]
pub fn stash<'a>(p: &'a mut i32, slot: &mut Option<&'a mut i32>) {
    *slot = Some(p);
}

// FALSE: `x` is left 5.
#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    stash(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

#[ensures(*p == old(*p))]
pub fn stash_old<'a>(p: &'a mut i32, slot: &mut Option<&'a mut i32>) {
    *slot = Some(p);
}

// FALSE: `x` is left 5.
#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_old_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    stash_old(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

// FALSE: the holder of `v` decides `^p`.
#[ensures(^p == *p)]
pub fn stash_push<'a>(p: &'a mut i32, v: &mut Vec<&'a mut i32>) {
    v.push(p);
}

// FALSE: the holder of `slot` decides `^p`.
#[ensures(^p == *p)]
pub fn stash_insert<'a>(p: &'a mut i32, slot: &mut Option<&'a mut i32>) {
    let _ = slot.insert(p);
}

#[ensures(^p == *p)]
pub fn give(p: &mut Cell<i32>) -> &Cell<i32> {
    &*p
}

// FALSE: the cell is left 5.
#[ensures(^x == *x)]
pub fn give_caller(x: &mut Cell<i32>) {
    let c = give(x);
    c.set(5);
}

fn main() {}
