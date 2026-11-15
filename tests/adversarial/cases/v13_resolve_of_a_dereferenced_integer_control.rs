//@ expect: verify
//@ xfail: `resolve(*x)` of `x: &mut i32` is the resolve of an integer, `true`, but the sort `&mut i32`
//@ xfail: is also the annotation of `b: Box<&mut i32>` and `s: Snapshot<&mut i32>`, whose `*b` and `*s`
//@ xfail: are borrows: D-127 refuses every dereference not through a shared reference to a value.
//@ mechanism: the price of D-127's operand rule: before it, this TRUE claim was read as the outer
//@ mechanism: borrow's resolve and left unknown.
//@ fixed-by: n/a (over-refusal guard, priced)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(resolve(*x))]
pub fn deref_int_after_write(x: &mut i32) {
    *x = 5;
}
