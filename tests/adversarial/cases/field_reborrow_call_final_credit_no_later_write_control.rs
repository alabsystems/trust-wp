//@ expect: verify
//@ mechanism: the field control for the credit rule: `&mut s.a` handed to the callee with
//@ mechanism: nothing written afterwards, so the field of the parameter's final value the
//@ mechanism: call pinned is what the program hands back. It is the twin of
//@ mechanism: field_reborrow_call_then_direct_write_final_stale with the write removed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub a: i32,
    pub b: i32,
}

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires((*s).a == 0i32)]
#[ensures((^s).a == 1i32)]
pub fn f(s: &mut S) {
    set(&mut s.a);
}
