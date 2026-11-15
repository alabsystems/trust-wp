//@ expect: verify
//@ mechanism: controls for the v11 cases: what D-109 refuses is a final value no lane may state,
//@ mechanism: however denoted. A `resolve` of a `&mut` whose final value the function states keeps
//@ mechanism: its reading, beside a parameter over interior-mutable memory too; a quantified
//@ mechanism: borrow in a clause that names no such parameter keeps its reading; a clause reading
//@ mechanism: the entry value in `old(..)` and the final value outside it keeps its reading; a
//@ mechanism: resolve of a by-value parameter is true, in a clause and in a loop invariant.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

pub struct S<'a> {
    pub c: &'a Cell<i32>,
}

#[ensures(resolve(x))]
pub fn untouched(x: &mut i32) {}

#[requires(*n < 100i32)]
#[ensures(^n == *n + 1i32)]
pub fn inc_beside_copy(n: &mut i32, x: &mut S<'_>) {
    *n += 1;
}

#[ensures(resolve(n))]
pub fn untouched_beside_cell(n: &mut i32, x: &mut Cell<i32>) {
    x.set(5);
}

// A `bool` borrow: a machine-integer one has its range stated on `*q` and
// `^q`, whose certificate ay withholds today
// (quantifier_binder_mut_borrow_of_machine_int_control.rs).
#[ensures(exists<q: &mut bool> q == b && ^q == !*q)]
pub fn flip_exists(b: &mut bool) {
    *b = !*b;
}

#[requires(*n < 100i32)]
#[ensures(resolve(x) && ^n == *n + 1i32)]
pub fn resolve_beside_inc(n: &mut i32, x: &mut i32) {
    *n += 1;
}

#[ensures(match (n, 0i32) { (q, _) => resolve(q) })]
pub fn tuple_match_untouched(n: &mut i32) {}

#[requires(*p < 100i32)]
#[ensures(*p == old(*p) + 1i32)]
pub fn inc_old(p: &mut i32) {
    *p += 1;
}

#[ensures(resolve(v))]
pub fn by_value(v: i32) {}

pub fn by_value_in_a_loop(v: i32) {
    let mut i = 0i32;
    #[invariant(resolve(v))]
    while i < 1 {
        i += 1;
    }
}
