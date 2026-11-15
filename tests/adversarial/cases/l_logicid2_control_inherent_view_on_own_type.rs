//@ expect: verify
//@ mechanism: logic-fn identity v2 — A::view called on an A receiver
//@ fixed-by: s35 logic-fn identity v2 (every local logic def has a unique id; method calls bind only by receiver type)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }
#[ensures(a.view() == 5)]
pub fn g(a: A) {}
