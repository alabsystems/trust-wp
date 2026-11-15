//@ expect: reject
//@ mechanism: A final read of a name the clause binds (`exists<q> q == x && ^q == *q`, a tuple
//@ mechanism: `match`/`let` of the parameter) and a `resolve` of a term holding the parameter
//@ mechanism: (`resolve(x.c)`, `resolve(*x)`, `resolve(&x)`) denote the final value of `x` without
//@ mechanism: spelling `^x`: D-108's refusal read `Final` nodes of the parameter's own name, so each
//@ mechanism: reached the mut-borrow lane, which keeps the entry value as `x`'s final value when the
//@ mechanism: `&Cell` is copied out of the referent before it is written.
//@ accept-means: the final value of a `&mut` over interior-mutable memory is stated through a
//@ accept-means: binder or a term holding it, and read as the entry value.
//@ WHY THE CONTRACT IS FALSE: each body leaves the cell the referent reaches at 5, whatever it held
//@ WHY THE CONTRACT IS FALSE: at entry; each clause claims `x` is left as it was (the quantified
//@ WHY THE CONTRACT IS FALSE: borrow equal to `x` is `x`; a resolve of a term holding `x` resolves it).
//@ fixed-by: D-109 (a final read of a bound name, in a clause naming a parameter whose final value
//@ fixed-by: is decided elsewhere, reads that one too; a resolve's operand is read by what it holds)
//@ teeth: MEASURED (debug driver, ay 0e44aed6a): 9da9f9a8 verifies all twelve functions (ACCEPTED);
//@ teeth: on D-109 every clause is refused by name.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

pub struct S<'a> {
    pub c: &'a Cell<i32>,
}

#[ensures(exists<q: &mut S<'_>> q == x && ^q == *q)]
pub fn exists_hat(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(exists<q: &mut S<'_>> q == x && resolve(q))]
pub fn exists_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(forall<q: &mut S<'_>> q == x ==> resolve(q))]
pub fn forall_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(match (x, 0i32) { (q, _) => resolve(q) })]
pub fn tuple_match_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(match Some(x) { Some(q) => resolve(q), None => true })]
pub fn option_match_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures({ let (q, _) = (x, 0i32); resolve(q) })]
pub fn let_tuple_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(resolve(x.c))]
pub fn field_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(resolve(*x))]
pub fn deref_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(resolve(&x))]
pub fn ref_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(resolve(x) == true)]
pub fn eq_true_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(!!resolve(x))]
pub fn notnot_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}

#[ensures(if resolve(x) { true } else { false })]
pub fn ite_resolve(x: &mut S<'_>) {
    let c = x.c;
    c.set(5);
}
