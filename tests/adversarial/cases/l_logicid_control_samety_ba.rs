//@ expect: verify
//@ mechanism: logic-fn identity — true twin: same-named types a::S / b::S each implementing the trait; call on b::S (definition order ba)
//@ fixed-by: s35 logic-fn identity
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr { #[logic] fn m(self) -> Int; }
pub mod b { use creusot_std::prelude::*; pub struct S; impl crate::Tr for S { #[logic(open)] fn m(self) -> Int { pearlite!{10} } } }
pub mod a { use creusot_std::prelude::*; pub struct S; impl crate::Tr for S { #[logic(open)] fn m(self) -> Int { pearlite!{0} } } }
#[ensures(result@ == s.m())]
pub fn f(s: b::S) -> u32 { 10 }
