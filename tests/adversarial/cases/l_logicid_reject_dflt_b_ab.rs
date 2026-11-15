//@ expect: reject
//@ mechanism: logic-fn identity — trait default body overridden by one impl; call on the overriding type (definition order ab)
//@ fixed-by: s35 logic-fn identity (type-directed receiver resolution, generic markers at call sites)
//@ accept-means: a clause was checked against a definition Rust would not select for that type
//@ teeth: accepted with exit 0 on wp-campaign fd7534d
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr2 { #[logic(open)] fn m(self) -> Int { pearlite!{0} } }
pub struct A;
pub struct B;
impl Tr2 for A {}
impl Tr2 for B { #[logic(open)] fn m(self) -> Int { pearlite!{10} } }
#[ensures(result@ == b.m())]
pub fn f(b: B) -> u32 { 0 }
