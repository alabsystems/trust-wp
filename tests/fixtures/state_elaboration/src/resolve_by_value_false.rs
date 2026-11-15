// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `resolve(x)` is the by-value `true` only of a value whose sort certainly
//! holds no borrow. Each function below except those marked TRUE claims a
//! borrow is resolved when another holder decides its final value: the
//! CALLER, who holds the returned borrow (spelled through the closure
//! postcondition `|r| ..`, which reads it as an unannotated `result`), or
//! the returned `Vec` holding it; or it asserts a snapshot of a borrow
//! resolved before the body writes it; or it claims resolved a borrow a
//! by-value struct holds in an `Option` field the body writes through
//! (itself or through the field); or it claims every borrow a quantifier
//! ranges over resolved, or the state of a closure it returns resolved; or,
//! a caller, it relies on such a claim. Every such claim is false.

#![allow(unused)]
#![feature(stmt_expr_attributes, proc_macro_hygiene)]

use trust_wp::prelude::*;

#[ensures(|r: &mut i32| resolve(r))]
pub fn closure_resolve(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r| resolve(r))]
pub fn closure_resolve_unannotated(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r: Option<&mut i32>| resolve(r))]
pub fn closure_resolve_some(x: &mut i32) -> Option<&mut i32> {
    Some(x)
}

#[ensures(|r: &mut i32| { let t = r; resolve(t) })]
pub fn closure_resolve_let(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r: &mut i32| resolve(r) && ^x == ^r && *r == *x)]
pub fn closure_give(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(true)]
pub fn write_five(x: &mut i32) {
    *x = 5;
}

// Returns 5: the caller writes 5 through the borrow `closure_give` claimed
// resolved.
#[ensures(result == 3i32)]
pub fn closure_give_caller() -> i32 {
    let mut a = 3i32;
    let r = closure_give(&mut a);
    write_five(r);
    a
}

#[ensures(|r: &mut i32| resolve(*r))]
pub fn closure_resolve_deref(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r: &mut i32| resolve(&r))]
pub fn closure_resolve_shared(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(resolve(result))]
pub fn vec_resolve(x: &mut i32) -> Vec<&mut i32> {
    let mut v = Vec::new();
    v.push(x);
    v
}

#[requires(*x != 5i32)]
pub fn snapshot_resolve(x: &mut i32) {
    let s = snapshot!(x);
    proof_assert!(resolve(*s));
    *x = 5;
}

#[requires(!*x)]
pub fn snapshot_resolve_bool(x: &mut bool) {
    let s = snapshot!(x);
    proof_assert!(resolve(*s));
    *x = true;
}

#[ensures(|r: &mut bool| resolve(r))]
pub fn closure_resolve_bool(x: &mut bool) -> &mut bool {
    x
}

pub struct Holder<'a> {
    pub o: Option<&'a mut i32>,
}

#[requires(match h.o { Some(ref p) => **p != 5i32, None => false })]
#[ensures(resolve(h))]
pub fn field_resolve(h: Holder<'_>) {
    if let Some(p) = h.o {
        *p = 5;
    }
}

#[requires(match h.o { Some(ref p) => **p != 5i32, None => false })]
#[ensures(resolve(h.o))]
pub fn field_projection_resolve(h: Holder<'_>) {
    if let Some(p) = h.o {
        *p = 5;
    }
}

#[ensures(!(exists<q: &mut i32> ^q != *q))]
pub fn quantified_resolve() {}

#[requires(f.precondition(()))]
#[ensures(exists<g: F> f.postcondition_mut((), g, ()) && resolve(g))]
pub fn closure_state_resolve<F: FnMut()>(mut f: F) -> F {
    f();
    f
}

#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32 && !(exists<q: &mut i32> !resolve(q)))]
pub fn quantified_beside_inc(x: &mut i32) {
    *x += 1;
}

#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32 && !(exists<x: &mut i32> !resolve(x)))]
pub fn quantified_shadowing(x: &mut i32) {
    *x += 1;
}

// TRUE: `b` is dropped untouched, so the borrow it holds ends where it was.
// Its final value is no symbol of the lane: refused, not refuted.
#[ensures(resolve(b))]
pub fn box_untouched(b: Box<&mut i32>) {}

// TRUE: the loop never writes `x`. The loop head names no final value of
// `x`: refused, not refuted with a fresh final.
pub fn loop_untouched(x: &mut i32) {
    let mut i = 0i32;
    #[invariant(resolve(x))]
    while i < 1 {
        i += 1;
    }
}

// TRUE: the standard reborrow contract.
#[ensures(|r: &mut i32| ^x == ^r && *r == *x)]
pub fn give(x: &mut i32) -> &mut i32 {
    x
}

// TRUE: a value holds no borrow.
#[ensures(resolve(v))]
pub fn value(v: i32) {}

// TRUE: nothing writes `x`.
#[ensures(resolve(x))]
pub fn untouched(x: &mut i32) {}

fn main() {}
