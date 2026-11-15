//@ expect: reject
//@ mechanism: A final value read inside `old(..)`: `in_the_pre_state` refused `old(^p)` only at a
//@ mechanism: call and only when spelled `^`. In the function's own lane the encoder reads
//@ mechanism: `resolve(x)` under `old` with the entry-state prefix, finds no final symbol for it
//@ mechanism: and reads it as the resolve of a by-value parameter: `true`.
//@ accept-means: a clause reading a final value in the entry state is credited as true whatever
//@ accept-means: the body leaves the borrow at.
//@ WHY THE CONTRACT IS FALSE: each body sets `*x` (or `x.a`) to 5 under a precondition that it was
//@ WHY THE CONTRACT IS FALSE: not 5, and `old(resolve(x))` is `old(*x) == ^x` (a prophecy does not
//@ WHY THE CONTRACT IS FALSE: depend on the state): the entry value is not the final one.
//@ fixed-by: D-109 (a final value read inside `old(..)`, however denoted, has no reading in either
//@ fixed-by: lane)
//@ teeth: MEASURED (debug driver, ay 0e44aed6a): 9da9f9a8 verifies old_resolve, old_resolve_and
//@ teeth: and old_resolve_struct (`old(^x == *x)`, the method and structural spellings were
//@ teeth: unknown there); on D-109 every clause is refused by name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{
    prelude::*,
    resolve::{structural_resolve, Resolve},
};

#[requires(*x != 5i32)]
#[ensures(old(resolve(x)))]
pub fn old_resolve(x: &mut i32) {
    *x = 5;
}

#[requires(*x != 5i32)]
#[ensures(old(resolve(x) && true))]
pub fn old_resolve_and(x: &mut i32) {
    *x = 5;
}

pub struct P {
    pub a: i32,
}

#[requires(x.a != 5i32)]
#[ensures(old(resolve(x)))]
pub fn old_resolve_struct(x: &mut P) {
    x.a = 5;
}

#[requires(*x != 5i32)]
#[ensures(old(^x == *x))]
pub fn old_hat(x: &mut i32) {
    *x = 5;
}

#[requires(*x != 5i32)]
#[ensures(old(x.resolve()))]
pub fn old_method(x: &mut i32) {
    *x = 5;
}

#[requires(*x != 5i32)]
#[ensures(old(structural_resolve(x)))]
pub fn old_structural(x: &mut i32) {
    *x = 5;
}
