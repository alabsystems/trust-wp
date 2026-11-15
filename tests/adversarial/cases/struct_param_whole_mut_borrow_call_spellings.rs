//@ expect: reject
//@ also-verified: reset
//@ mechanism: the spellings struct_param_whole_mut_borrow_call_keeps_entry_value.rs names beside its
//@ mechanism: own: a by-value struct parameter borrowed whole through a named reborrow
//@ mechanism: (`let r = &mut s; reset(r);`), and an `ensures` comparing the result with the
//@ mechanism: parameter's entry value with no `requires` at all. In each the value the parameter
//@ mechanism: holds after the borrow was read as its entry value.
//@ fixed-by: D-241: the value a by-value struct parameter holds after a `&mut` borrow of it ends is named apart from its entry value in the function lane.
//@ accept-means: a claim about a by-value struct parameter after a call overwrote it through
//@ accept-means: `&mut` is discharged by its entry value.
//@ WHY THE CONTRACT IS FALSE: `reset` sets `a` to 4; `named(P { a: 3, b: 0 })` returns 4 and
//@ WHY THE CONTRACT IS FALSE: claims 3, and `vs_entry(P { a: 0, b: 0 })` returns 4 and claims 0.
//@ teeth: MEASURED: both functions verified before D-241, both FAILED with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: i32,
    pub b: i32,
}

#[ensures(true)]
pub fn reset(t: &mut P) {
    t.a = 4;
}

#[requires(s.a@ == 3)]
#[ensures(result@ == 3)]
pub fn named(mut s: P) -> i32 {
    let r = &mut s;
    reset(r);
    s.a
}

#[ensures(result@ == s.a@)]
pub fn vs_entry(mut s: P) -> i32 {
    reset(&mut s);
    s.a
}
