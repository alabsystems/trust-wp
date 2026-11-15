//@ expect: reject
//@ mechanism: Creusot's `ViewRel::rel_mono` is a law with `#[requires(Self::rel(a, f1))]` and `#[requires(f2.incl(f1))]` (creusot-std `logic/ra/view.rs`), so a logic body that invokes it owes both. The standard library this crate builds against declares the trait method with no contract, so the call owed nothing. The walk's standard-library table now refuses `rel_mono`, `rel_none` and `get_timestamp_monotonic`.
//@ accept-means: a monotonicity law invoked on fragments it does not relate is credited.
//@ WHY IT IS FALSE: nothing relates `a` and `f1`, nor includes `f1` in `f2`; Creusot's `vc_caller` owes both and is invalid.
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
pub fn caller<R: ViewRel>(a: Option<R::Auth>, f1: R::Frag, f2: R::Frag) -> Int {
    R::rel_mono(a, f1, f2);
    0
}
