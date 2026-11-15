//@ expect: reject
//@ mechanism: logic-fn identity v2 — u32 overrides the default with false; x.logic_default() on u32 must bind the override
//@ fixed-by: s35 logic-fn identity v2 (Instance-resolved inherited default bodies)
//@ accept-means: a trait default body answered a call whose receiver's impl overrides it
//@ teeth: none — rejected on wp-campaign 21c018a1 too; guard for the inherited-default rule
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait T { #[logic(open)] fn logic_default(self) -> bool { true } }
impl T for u32 { #[logic(open)] fn logic_default(self) -> bool { false } }
impl T for u64 {}
#[ensures(x.logic_default())]
pub fn g(x: u32) {}
