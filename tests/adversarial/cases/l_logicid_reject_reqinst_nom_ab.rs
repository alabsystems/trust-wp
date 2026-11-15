//@ expect: reject
//@ mechanism: logic-fn identity — generic callee requires t.m() == u.m() instantiated at newtypes A(u32)/B(u32) (erased to Int) (definition order ab)
//@ fixed-by: s35 logic-fn identity (type-directed receiver resolution, generic markers at call sites)
//@ accept-means: a clause was checked against a definition Rust would not select for that type
//@ teeth: accepted with exit 0 on wp-campaign fd7534d
//@ also-verified: g
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr { #[logic] fn m(self) -> Int; }
pub struct A(pub u32);
pub struct B(pub u32);
impl Tr for A { #[logic(open)] fn m(self) -> Int { pearlite!{0} } }
impl Tr for B { #[logic(open)] fn m(self) -> Int { pearlite!{10} } }
#[requires(t.m() == u.m())]
pub fn g<T: Tr, U: Tr>(t: T, u: U) {}
#[ensures(true)]
pub fn caller() { g(A(3), B(3)) }
