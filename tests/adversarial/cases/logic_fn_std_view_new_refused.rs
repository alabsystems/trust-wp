//@ expect: reject
//@ mechanism: Creusot's `View::new` is `#[logic] #[requires(R::rel(auth, frag))]` (creusot-std `logic/ra/view.rs`), so a logic body that calls it owes the view relation at the call. The standard library this crate builds against declares `View::new` as an open logic function with no contract, so no clause reached the callee-precondition walk and the call owed nothing. The walk's standard-library table now refuses `View::new`, whose precondition it cannot state for an arbitrary `R`.
//@ accept-means: a view built from an authority and a fragment its relation may not relate is credited.
//@ WHY IT IS FALSE: nothing relates `a` and `f`; Creusot's `vc_caller` owes `R::rel(a, f)` for every `R: ViewRel` and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-119's callee-precondition walk and before this table entry: `creusot_test::caller verified ✓`.
//@ fixed-by: D-119 — a standard logic function whose precondition the walk cannot state is refused.
//@ verdict: unknown
//@ refused-with: to a standard logic function whose precondition the logic lane cannot state
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::logic::ra::view::{View, ViewRel};
use creusot_std::prelude::*;

#[logic]
#[ensures(true)]
pub fn caller<R: ViewRel>(a: Option<R::Auth>, f: R::Frag) -> View<R> {
    View::new(a, f)
}
