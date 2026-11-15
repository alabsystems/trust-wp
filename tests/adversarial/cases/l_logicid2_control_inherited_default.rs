//@ expect: verify
//@ mechanism: logic-fn identity v2 — impl T for u32 {} inherits a self-contained default body; x.logic_default() on u32 is that body
//@ fixed-by: s35 logic-fn identity v2 (Instance-resolved inherited default bodies)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait T { #[logic(open)] fn logic_default(self) -> bool { true } }
impl T for u32 {}
#[ensures(x.logic_default())]
pub fn g(x: u32) {}
