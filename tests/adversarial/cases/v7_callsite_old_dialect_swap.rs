//@ expect: reject
//@ mechanism: a callee postcondition in the pre-Creusot dialect (it names a `&mut` parameter
//@ mechanism: inside `old(..)`, so every bare `*a` is the value `a` is left with) is proved by the
//@ mechanism: callee's own lane under that reading, and instantiated at the call site in the
//@ mechanism: Creusot reading (`*a` the value at the call). The caller learns
//@ mechanism: `pre(x) == pre(y) && pre(y) == pre(x)`, a consistent but false premise.
//@ accept-means: a caller of the documented `swap` contract proves its two arguments equal at entry.
//@ WHY THE CONTRACT IS FALSE: with *x = 1, *y = 2 at entry, `*x == *y` (the entry values) is false.
//@ fixed-by: D-101 (a call reads a callee clause through the state elaboration its own lane proves it under)
//@ teeth: MEASURED on d73d0571 (debug driver): ACCEPTED, `swap_caller verified`. On the D-101 tree:
//@ teeth: unknown; its control v7_callsite_old_dialect_swap_control verifies there (it was unknown).
//@ also-verified: swap
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(*a == old(*b) && *b == old(*a))]
pub fn swap(a: &mut i32, b: &mut i32) {
    let t = *a;
    *a = *b;
    *b = t;
}

#[ensures(*x == *y)]
pub fn swap_caller(x: &mut i32, y: &mut i32) {
    swap(x, y)
}
