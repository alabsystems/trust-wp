//@ expect: verify
//@ mechanism: a reordered enum-variant pattern with DISTINCT field types whose contract is TRUE
//@ mechanism: under the correct binding. The live defect cuts both ways: reading `{b: bb, a: _aa}`
//@ mechanism: positionally binds `bb` to the u32 field, so a TRUE statement about `b: A` is
//@ mechanism: unprovable. This must verify once the order is resolved.
//@ accept-means: n/a (control) — `bb` names `b: A` and `A::view()` is 5 by definition.
//@ teeth: n/a — over-refusal control; does NOT verify while the defect is live.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }
pub enum T { C { a: u32, b: A }, N }
#[ensures(match t { T::C { b: bb, a: _aa } => bb.view() == 5, T::N => true })]
pub fn g(t: T) {}
