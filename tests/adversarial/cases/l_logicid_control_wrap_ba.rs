//@ expect: verify
//@ mechanism: logic-fn identity — true twin: impls for W<u8>/W<i8> (one solver sort name); call on W<i8> (definition order ba)
//@ fixed-by: s35 logic-fn identity
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr { #[logic] fn m(self) -> Int; }
pub struct W<T>(pub T);
impl Tr for W<i8> { #[logic(open)] fn m(self) -> Int { pearlite!{10} } }
impl Tr for W<u8> { #[logic(open)] fn m(self) -> Int { pearlite!{0} } }
#[ensures(result@ == w.m())]
pub fn f(w: W<i8>) -> u32 { 10 }
