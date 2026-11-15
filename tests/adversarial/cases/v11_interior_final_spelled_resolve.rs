//@ expect: reject
//@ mechanism: D-108 refused a final value of a `&mut` parameter over interior-mutable memory by
//@ mechanism: its SPELLING: `state::first_final_decided_elsewhere` collected only `PureExpr::Final`
//@ mechanism: nodes. `resolve(x)` is the same claim (`*x == ^x`; the encoder expands it to
//@ mechanism: `x_current == x_final`) and names no `^`, so the clause reached the mut-borrow lane,
//@ mechanism: which keeps the entry value as the final value when the `&Cell` is copied out of the
//@ mechanism: referent before it is written. Every spelling of the final value now goes through one
//@ mechanism: predicate (`FinalReaders::final_operands`): `resolve` by any path or as a method,
//@ mechanism: `structural_resolve`, a logic function reading `^q` or `resolve(q)`, an alias.
//@ accept-means: a write through interior mutability reachable from a `&mut` parameter's referent
//@ accept-means: is invisible to the value that parameter is left with when the final value is
//@ accept-means: spelled other than `^x`.
//@ WHY THE CONTRACT IS FALSE: each body leaves the cell the referent reaches at 5, whatever it held
//@ WHY THE CONTRACT IS FALSE: at entry: the same bodies and reading as
//@ WHY THE CONTRACT IS FALSE: v10_interior_write_through_copied_shared_ref, whose `^x == *x`
//@ WHY THE CONTRACT IS FALSE: D-108 refuses by name.
//@ fixed-by: D-109 (what denotes a final value is decided by one predicate the state elaboration
//@ fixed-by: reads, not by the spelling `^`)
//@ teeth: MEASURED (debug driver, ay 0e44aed6a): 9da9f9a8 verifies copy_field_set, copy_tuple_set,
//@ teeth: copy_option_set, copy_option_match, copy_array_set, boxed_copy_set, nested_copy_set,
//@ teeth: resolve_and, resolve_let and resolve_match (the method, UFCS, path and structural
//@ teeth: spellings were unknown there, the logic functions refused at the encoder's door); on
//@ teeth: D-109 every clause is refused by name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::{
    prelude::*,
    resolve::{structural_resolve, Resolve},
};

pub struct S<'a> {
    pub c: &'a Cell<i32>,
}

pub struct W<'a> {
    pub s: S<'a>,
}

#[logic(open, prophetic)]
pub fn unchanged<T>(q: &mut T) -> bool {
    pearlite! { ^q == *q }
}

#[logic(open, prophetic)]
pub fn settled<T>(q: &mut T) -> bool {
    pearlite! { resolve(q) }
}

#[ensures(resolve(x))]
pub fn copy_field_set(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(resolve(x))]
pub fn copy_tuple_set(x: &mut (u8, &Cell<i32>)) {
    let (_, c) = *x;
    c.set(5);
}

#[ensures(resolve(x))]
pub fn copy_option_set(x: &mut Option<&Cell<i32>>) {
    if let Some(c) = *x {
        c.set(5);
    }
}

#[ensures(resolve(x))]
pub fn copy_option_match(x: &mut Option<&Cell<i32>>) {
    match *x {
        Some(c) => c.set(5),
        None => {}
    }
}

#[ensures(resolve(x))]
pub fn copy_array_set(x: &mut [&Cell<i32>; 1]) {
    let c = x[0];
    c.set(5);
}

#[ensures(resolve(x))]
pub fn boxed_copy_set(x: &mut Box<S<'_>>) {
    let c = x.c;
    c.set(5);
}

#[ensures(resolve(x))]
pub fn nested_copy_set(x: &mut W<'_>) {
    let c = x.s.c;
    c.set(5);
}

#[ensures(resolve(x) && true)]
pub fn resolve_and(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures({ let t = x; resolve(t) })]
pub fn resolve_let(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(match x { t => resolve(t) })]
pub fn resolve_match(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(x.resolve())]
pub fn resolve_method(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(Resolve::resolve(x))]
pub fn resolve_ufcs(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(structural_resolve(x))]
pub fn resolve_structural(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(unchanged(x))]
pub fn logic_final(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(settled(x))]
pub fn logic_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}
