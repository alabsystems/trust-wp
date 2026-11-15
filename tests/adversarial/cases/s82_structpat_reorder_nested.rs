//@ expect: reject
//@ mechanism: a reordered enum-variant pattern NESTED inside another named-field pattern. The
//@ mechanism: outer pattern resolves; the inner `E::C { b: bb, a: aa }` does not, so `aa` is
//@ mechanism: positioned at index 0 of the variant and typed as `A`.
//@ accept-means: the rewrite's recursion resolves the outer shell and leaves the inner one
//@ accept-means: guessing at source order.
//@ WHY THE CONTRACT IS FALSE: `aa` binds `a: u32`; `W { e: E::C { a: 0, b: A } }` has `aa@ == 0`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }
pub enum E { C { a: u32, b: A }, N }
pub struct W { pub e: E, pub k: u32 }
#[ensures(match w { W { k: _kk, e: inner } => match inner { E::C { b: bb, a: aa } => aa.view() == 5, E::N => true } })]
pub fn g(w: W) {}
