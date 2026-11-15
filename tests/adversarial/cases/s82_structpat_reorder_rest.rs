//@ expect: reject
//@ mechanism: a reordered named-field pattern combined with a `..` rest pattern. The contract
//@ mechanism: parser drops the field-name metadata entirely when `..` is present
//@ mechanism: (contract_parser/helpers/patterns.rs: `has_rest`), so the driver cannot even see
//@ mechanism: that `b` is not field 0. `bb` is then positioned at index 0 and typed as `A`.
//@ accept-means: a rest pattern silently binds the FIRST declared field whatever was named.
//@ WHY THE CONTRACT IS FALSE: `bb` binds `b: u32`, and `g(S3 { a: A, b: 0 })` has `bb@ == 0`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }
pub struct S3 { pub a: A, pub b: u32 }
#[ensures(match s { S3 { b: bb, .. } => bb.view() == 5 })]
pub fn g(s: S3) {}
