//@ expect: verify
//@ mechanism: logic-fn identity — two impls of one trait's logic method; receiver-style call on the FIRST impl's type (definition order ba)
//@ fixed-by: s35 logic-fn identity (unique ids + owner-scope resolution + receiver dispatch)
//@ accept-means: n/a (control): the true claim about the resolved definition must verify
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr { #[logic] fn m(self) -> Int; }
pub struct A;
pub struct B;
impl Tr for B { #[logic(open)] fn m(self) -> Int { pearlite!{10} } }
impl Tr for A { #[logic(open)] fn m(self) -> Int { pearlite!{0} } }
#[ensures(result@ == a.m())]
pub fn f(a: A) -> u32 { 0 }
