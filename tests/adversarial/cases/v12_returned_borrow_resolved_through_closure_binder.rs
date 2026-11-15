//@ expect: reject
//@ mechanism: `applied_to_the_result` desugars the closure postcondition `|r: T| body` to
//@ mechanism: `body[r := result]` with `result` unannotated (the closure parameter's sort is not
//@ mechanism: carried), and `encode_resolve` read an unannotated variable the lane named no current
//@ mechanism: or final state of as a by-value parameter: `resolve(result)` was `true`. The same claim
//@ mechanism: spelled `resolve(result)` carries the return type's sort and was unknown.
//@ accept-means: a function returning its `&mut` argument (or `Some` of it) is credited with the
//@ accept-means: claim that the returned borrow is resolved at the return.
//@ WHY THE CONTRACT IS FALSE: the caller holding the returned borrow decides its final value after
//@ WHY THE CONTRACT IS FALSE: the call (it may write through it), so `*result == ^result` is no fact
//@ WHY THE CONTRACT IS FALSE: of the function.
//@ fixed-by: D-126 (`resolve` is the by-value `true` only of an annotated variable whose sort's
//@ fixed-by: shape holds no borrow; unannotated, it is read through the lane's final value)
//@ teeth: The r11 review measured (ay 0e44aed6a) c_resolve, give_unann, cl_opt, rb_closure_let
//@ teeth: and give2 verified on 6a828d52. MEASURED (debug driver, ay 57a37e51): bdbba131
//@ teeth: verifies c_resolve, give_unann, cl_opt, rb_closure_let, give2, closure_deref,
//@ teeth: closure_shared, give3 and c_resolve_bool (ACCEPTED); on D-126 each is refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{prelude::*, resolve::Resolve};

#[ensures(|r: &mut i32| resolve(r))]
pub fn c_resolve(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r| resolve(r))]
pub fn give_unann(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r: Option<&mut i32>| resolve(r))]
pub fn cl_opt(x: &mut i32) -> Option<&mut i32> {
    Some(x)
}

#[ensures(|r: &mut i32| { let t = r; resolve(t) })]
pub fn rb_closure_let(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r: &mut i32| resolve(r) && ^x == ^r && *r == *x)]
pub fn give2(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r: &mut i32| resolve(*r))]
pub fn closure_deref(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r: &mut i32| resolve(&r))]
pub fn closure_shared(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r: &mut i32| ^x == ^r && *r == *x && resolve(r))]
pub fn give3(x: &mut i32) -> &mut i32 {
    x
}

#[ensures(|r: &mut bool| resolve(r))]
pub fn c_resolve_bool(x: &mut bool) -> &mut bool {
    x
}
