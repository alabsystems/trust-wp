// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A borrow stored where another parameter's holder writes it, under a slot
//! type or an outlives bound the signature analysis once did not read: a
//! projection naming the borrow's late-bound region, the implied bound of the
//! return type, the implied bound of an impl header. Every caller writes 5
//! through the slot under `*x != 5`: every caller's contract is false.

#![allow(unused)]

use std::marker::PhantomData;

use trust_wp::prelude::*;

pub trait Tr<'a> {
    type Slot;
}

impl<'a> Tr<'a> for () {
    type Slot = Option<&'a mut i32>;
}

#[ensures(^p == *p)]
pub fn stash_proj<'a>(p: &'a mut i32, slot: &mut <() as Tr<'a>>::Slot) {
    *slot = Some(p);
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_proj_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    stash_proj(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

#[ensures(^p == *p)]
pub fn stash_ret<'a, 'b>(p: &'a mut i32, slot: &mut Option<&'b mut i32>) -> Option<&'b &'a ()> {
    *slot = Some(p);
    None
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_ret_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    let _ = stash_ret(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

pub struct P<'a, 'b>(PhantomData<&'b &'a ()>);

impl<'a, 'b> P<'a, 'b> {
    #[ensures(^p == *p)]
    pub fn stash(p: &'a mut i32, slot: &mut Option<&'b mut i32>) {
        *slot = Some(p);
    }
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_impl_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    P::stash(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

fn main() {}
