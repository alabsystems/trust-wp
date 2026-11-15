//@ expect: reject
//@ mechanism: a callee in the pre-Creusot dialect whose `old(..)` reads prove nothing
//@ mechanism: (`old(*p) - old(*p) == 0`) still marks the dialect, so its `*p == v` is the value
//@ mechanism: `p` is left with. The call read `*p` as the value at the call: the caller learned its
//@ mechanism: argument's entry value is `v`.
//@ accept-means: the entry value of a `&mut` argument is the value a callee stores into it.
//@ WHY THE CONTRACT IS FALSE: the entry value of `*q` is arbitrary.
//@ fixed-by: D-101
//@ teeth: MEASURED on d73d0571 (debug driver): `set_caller verified`. On the D-101 tree: unknown;
//@ teeth: `^q == 9` verifies there (tests/fixtures/state_elaboration call_old_dialect_true).
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(*p == v && old(*p) - old(*p) == 0i32)]
pub fn set(p: &mut i32, v: i32) {
    *p = v;
}

#[ensures(*q == 9i32)]
pub fn set_caller(q: &mut i32) {
    set(q, 9)
}
