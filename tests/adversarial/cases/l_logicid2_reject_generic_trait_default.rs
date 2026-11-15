//@ expect: reject
//@ mechanism: logic-fn identity v2 — generic trait T<X>: the override for T<u16> must not be answered by the default inherited by T<u8>
//@ fixed-by: s35 logic-fn identity v2 (Instance-resolved inherited default bodies)
//@ accept-means: a trait default body answered a call whose receiver's impl overrides it
//@ teeth: none — rejected on wp-campaign 21c018a1 too; guard for the inherited-default rule
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait T<X> { #[logic(open)] fn logic_default(self) -> bool { true } }
impl T<u8> for u32 {}
impl T<u16> for u32 { #[logic(open)] fn logic_default(self) -> bool { false } }
#[ensures(<u32 as T<u16>>::logic_default(x))]
pub fn g(x: u32) {}
