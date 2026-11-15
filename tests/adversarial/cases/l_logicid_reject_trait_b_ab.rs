//@ expect: reject
//@ mechanism: logic-fn identity — two impls of one trait's logic method; receiver-style call on the SECOND impl's type (definition order ab)
//@ fixed-by: s35 logic-fn identity (unique ids + owner-scope resolution + receiver dispatch)
//@ accept-means: a clause was checked against another definition that shares the short name
//@ teeth: accepted with exit 0 on wp-campaign fd7534d in at least one definition order (see s35 progress.md)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr { #[logic] fn m(self) -> Int; }
pub struct A;
pub struct B;
impl Tr for A { #[logic(open)] fn m(self) -> Int { pearlite!{0} } }
impl Tr for B { #[logic(open)] fn m(self) -> Int { pearlite!{10} } }
#[ensures(result@ == b.m())]
pub fn f(b: B) -> u32 { 0 }
