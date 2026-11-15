//@ expect: verify
//@ mechanism: logic-fn identity v2 — u.view() == u@ on u32 through View while a local inherent A::view exists
//@ fixed-by: s35 logic-fn identity v2 (every local logic def has a unique id; method calls bind only by receiver type)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
impl A { #[logic(open)] pub fn view(self) -> Int { pearlite!{5} } }
#[ensures(u.view() == u@)]
pub fn g(u: u32) {}
