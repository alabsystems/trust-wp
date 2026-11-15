//@ expect: reject
//@ also-verified: reset, scramble
//@ mechanism: a by-value struct parameter lent whole to two calls in turn. D-241 names the value the
//@ mechanism: first borrow hands back (`^s`) apart from the entry value; the second borrow reads that
//@ mechanism: value and hands back `^^s`, which the encoder collapses onto its operand like any `^v` of a
//@ mechanism: plain datatype value. Renamed one level only, `^^s` is the first call's result: the
//@ mechanism: second call did nothing.
//@ accept-means: a claim about a by-value struct parameter after two calls overwrote it through `&mut`
//@ accept-means: is discharged by what the first call left.
//@ WHY THE CONTRACT IS FALSE: `scramble` sets `a` to 7; `two_calls(..)` returns 7 and claims 4.
//@ fixed-by: D-241: each borrow's final value of a lent by-value parameter is a symbol of its own.
//@ teeth: MEASURED: FAILED on D-240 (both finals collapse onto the entry value, which nothing pins),
//@ teeth: verified with the one-level rename, FAILED with D-241.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: i32,
    pub b: i32,
}

#[ensures((^t).a@ == 4)]
#[ensures((^t).b@ == (*t).b@)]
pub fn reset(t: &mut P) {
    let b = t.b;
    *t = P { a: 4, b };
}

#[ensures(true)]
pub fn scramble(t: &mut P) {
    t.a = 7;
}

#[ensures(result@ == 4)]
pub fn two_calls(mut s: P) -> i32 {
    reset(&mut s);
    scramble(&mut s);
    s.a
}
