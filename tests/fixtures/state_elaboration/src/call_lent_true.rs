// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A shared reborrow of a `&mut` parameter's referent is no borrow the
//! result's holder can write through, so the value the parameter is left
//! with is the value at return, in the callee's lane and at each call.

#![allow(unused)]

use trust_wp::prelude::*;

#[ensures(*p == old(*p) + 1i32)]
pub fn inc_peek(p: &mut i32) -> &i32 {
    *p += 1;
    &*p
}

// TRUE.
#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32)]
pub fn inc_peek_caller(x: &mut i32) {
    let _ = inc_peek(x);
}

fn main() {}
