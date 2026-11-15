//@ expect: reject
//@ mechanism: the s77rev shape on a PLAIN STRUCT rather than an enum variant. The pattern
//@ mechanism: `S { b: bb, a: aa }` is written in non-declaration order; if the driver types
//@ mechanism: pattern fields positionally in SOURCE order, `aa` is typed as `A` and
//@ mechanism: `A::view()` answers 5 for a binding that is really a u32.
//@ accept-means: the struct arm of the field-order rewrite is as blind as the enum arm.
//@ WHY THE CONTRACT IS FALSE: `aa` binds `a: u32`, and `g(S { a: 0, b: A })` has `aa@ == 0`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }
pub struct S { pub a: u32, pub b: A }
#[ensures(match s { S { b: bb, a: aa } => aa.view() == 5 })]
pub fn g(s: S) {}
