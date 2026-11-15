//@ expect: reject
//@ mechanism: A quantifier's binder is one bound term, and the wrapper collapsed both `*q` and `^q`
//@ mechanism: of a binder that is neither a match binder nor a prophecy carrier onto it, whatever
//@ mechanism: its sort: over `q: &mut i32` (or `&mut T`), `^q == *q` and `resolve(q)` were
//@ mechanism: `q == q`, true of every borrow the quantifier ranges over.
//@ accept-means: a claim that every `&mut i32` is resolved (no borrow's final value differs from
//@ accept-means: its current value) is credited, alone or beside a true claim of a parameter.
//@ WHY THE CONTRACT IS FALSE: a borrow whose final value differs from its current value exists
//@ WHY THE CONTRACT IS FALSE: (any `&mut` written through after it is taken), so
//@ WHY THE CONTRACT IS FALSE: `exists<q: &mut i32> !resolve(q)` holds and its negation does not.
//@ fixed-by: D-126 (the final value of a quantifier's binder annotated at a sort whose shape may
//@ fixed-by: hold a borrow is refused, not collapsed onto the binder)
//@ teeth: MEASURED (debug driver, ay 57a37e51): bdbba131 verifies none_unresolved, none_moved,
//@ teeth: inc_and_none, none_moved_generic and shadowing_binder (ACCEPTED); on D-126 each is
//@ teeth: refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{prelude::*, resolve::Resolve};

#[ensures(!(exists<q: &mut i32> !resolve(q)))]
pub fn none_unresolved() {}

#[ensures(!(exists<q: &mut i32> ^q != *q))]
pub fn none_moved() {}

#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32 && !(exists<q: &mut i32> !resolve(q)))]
pub fn inc_and_none(x: &mut i32) {
    *x += 1;
}

#[ensures(!(exists<q: &mut T> ^q != *q))]
pub fn none_moved_generic<T>() {}

#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32 && !(exists<x: &mut i32> !resolve(x)))]
pub fn shadowing_binder(x: &mut i32) {
    *x += 1;
}
