//@ expect: verify
//@ mechanism: logic-fn identity v2 — a local DeepModel impl used on its own type (a.deep_model() binds <A as DeepModel>::deep_model)
//@ fixed-by: s35 logic-fn identity v2 (every local logic def has a unique id; method calls bind only by receiver type)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl DeepModel for A { type DeepModelTy = Int; #[logic(open)] fn deep_model(self) -> Int { pearlite!{ 7 } } }
#[ensures(a.deep_model() == 7)]
pub fn g(a: A) {}
