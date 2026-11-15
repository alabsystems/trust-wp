//@ expect: verify
//@ mechanism: logic-fn identity — true twin: local `a.view()` uses A's impl and `u.view()` on u32 is the model view
//@ fixed-by: s35 logic-fn identity
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl View for A { type ViewTy = Int; #[logic(open)] fn view(self) -> Int { pearlite!{0} } }
#[requires(a.view() == 0 && u.view() == 7)]
pub fn g(a: A, u: u32) {}
#[ensures(true)]
pub fn caller() { g(A, 7u32) }
