// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A pre-Creusot clause's bare `*p` is the value `p` is left with; when the
//! result may borrow `p` (a raw pointer, a type whose fields reach one, a
//! type past `mut_borrow::may_carry_borrow`'s depth bound) that value is
//! whoever holds the result's to decide. A function's own lane read such a
//! `*p` at entry, proving each callee's false `*p == old(*p)` as `entry ==
//! entry`, and the call, deciding lending from the return type's regions
//! alone, read it as the value after the call, crediting each caller with
//! `^x == *x`. A shared reference to a `Cell` lends one too. Every contract
//! below is false.

#![allow(unused)]

use std::{cell::Cell, rc::Rc};

use trust_wp::prelude::*;

#[ensures(*p == old(*p))]
pub fn leak(p: &mut i32) -> *mut i32 {
    *p = 5;
    p as *mut i32
}

// FALSE: `x` is left 5.
#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn leak_caller(x: &mut i32) {
    let _ = leak(x);
}

#[ensures(*p == old(*p))]
pub fn share(p: &mut i32) -> Rc<i32> {
    *p = 5;
    Rc::new(*p)
}

// FALSE: `x` is left 5.
#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn share_caller(x: &mut i32) {
    let _ = share(x);
}

pub struct Handle {
    pub ptr: *mut i32,
}

#[ensures(*p == old(*p))]
pub fn leak_handle(p: &mut i32) -> Handle {
    *p = 7;
    Handle { ptr: p as *mut i32 }
}

// FALSE: `x` is left 7.
#[requires(*x != 7i32)]
#[ensures(^x == *x)]
pub fn leak_handle_caller(x: &mut i32) {
    let _ = leak_handle(x);
}

#[ensures(*p == old(*p) + 1i32)]
pub fn bump_and_list(p: &mut i32) -> Vec<i32> {
    *p += 2;
    vec![*p]
}

// FALSE: `x` is left two more.
#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32)]
pub fn bump_and_list_caller(x: &mut i32) {
    let _ = bump_and_list(x);
}

pub struct Tag {
    pub id: i32,
    pub next: Option<Box<Tag>>,
}

#[ensures(*p == old(*p))]
pub fn tag(p: &mut i32) -> Tag {
    *p = 5;
    Tag { id: *p, next: None }
}

// FALSE: `x` is left 5.
#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn tag_caller(x: &mut i32) {
    let _ = tag(x);
}

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

// FALSE for `T = U`: `x` is left 5.
#[ensures(^x == *x)]
pub fn generic_caller<T: Leak2>(t: &T, x: &mut i32) {
    let _ = t.leak2(x);
}

// FALSE: `x` is left 5.
#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn concrete_caller(x: &mut i32) {
    let _ = U.leak2(x);
}

// A shared reference lends a borrow when its referent has interior
// mutability: the holder of the returned `&Cell` writes the cell.
#[ensures(*p == old(*p))]
pub fn give(p: &mut Cell<i32>) -> &Cell<i32> {
    &*p
}

// FALSE: `x` is left 5.
#[ensures(^x == *x)]
pub fn give_caller(x: &mut Cell<i32>) {
    let c = give(x);
    c.set(5);
}

fn main() {}
