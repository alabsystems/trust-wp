//@ expect: verify
//@ mechanism: the control for l_logicid3_reject_match_arm_variant_types — the same match, each
//@ mechanism: arm asserting the value of the definition its OWN field type selects. Both arms
//@ mechanism: spell `_.val()`, and the two spellings must resolve to two different definitions.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
pub struct B;
impl A { #[logic(open)] pub fn val(self) -> Int { pearlite!{5} } }
impl B { #[logic(open)] pub fn val(self) -> Int { pearlite!{7} } }
pub enum E { One(A), Two(B) }
#[ensures(match e { E::One(x) => x.val() == 5, E::Two(y) => y.val() == 7 })]
pub fn g(e: E) {}
