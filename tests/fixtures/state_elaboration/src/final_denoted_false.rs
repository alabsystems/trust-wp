// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A final value is denoted by `^x`, by `resolve(x)` (`*x == ^x`) spelled
//! any way, by a logic function reading one, by a quantified borrow equal to
//! `x`, and it is read in the entry state inside `old(..)` and at a loop
//! head. Every function below except the three marked TRUE claims a borrow
//! is left as it was when its body writes it (a cell reached through a
//! copied `&Cell`, or `*x = 5` under `*x != 5`): every such contract, or
//! loop invariant, is false.

#![allow(unused)]
#![feature(stmt_expr_attributes, proc_macro_hygiene)]

use std::cell::Cell;

use trust_wp::prelude::*;

pub struct S<'a> {
    pub c: &'a Cell<i32>,
}

#[logic(open, prophetic)]
pub fn unchanged<T>(q: &mut T) -> bool {
    pearlite! { ^q == *q }
}

#[ensures(resolve(x))]
pub fn copy_set_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(match (x, 0i32) { (q, _) => resolve(q) })]
pub fn copy_set_tuple_match(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(exists<q: &mut S<'_>> q == x && ^q == *q)]
pub fn copy_set_exists(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(unchanged(x))]
pub fn copy_set_logic(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[requires(*x != 5i32)]
#[ensures(old(resolve(x)))]
pub fn set5_old_resolve(x: &mut i32) {
    *x = 5;
}

// TRUE: nothing writes `x`.
#[ensures(resolve(x))]
pub fn untouched(x: &mut i32) {}

// TRUE: `n` is not over interior-mutable memory.
#[requires(*n < 100i32)]
#[ensures(^n == *n + 1i32)]
pub fn inc_beside_copy(n: &mut i32, x: &mut S<'_>) {
    *n += 1;
}

// TRUE: a quantified borrow in a clause naming no parameter over
// interior-mutable memory keeps its reading. A `bool` borrow: a
// machine-integer one has its range stated on `*q` and `^q`, whose
// certificate ay withholds today
// (quantifier_binder_mut_borrow_of_machine_int_control.rs).
#[ensures(exists<q: &mut bool> q == b && ^q == !*q)]
pub fn flip_exists(b: &mut bool) {
    *b = !*b;
}

// Refuted, not verified: last, so no refutation cuts the rest short.
#[requires(*x != 5i32)]
pub fn set5_loop_resolve(x: &mut i32) {
    let mut i = 0i32;
    #[invariant(resolve(x))]
    while i < 1 {
        *x = 5;
        i += 1;
    }
}

fn main() {}
