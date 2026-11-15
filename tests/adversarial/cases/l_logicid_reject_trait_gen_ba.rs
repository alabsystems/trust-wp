//@ expect: reject
//@ mechanism: logic-fn identity — generic `t.m()` for `T: Tr` must stay on the opaque trait declaration, not an impl body (definition order ba)
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
impl Tr for B { #[logic(open)] fn m(self) -> Int { pearlite!{10} } }
impl Tr for A { #[logic(open)] fn m(self) -> Int { pearlite!{0} } }
#[ensures(result@ == t.m())]
pub fn f<T: Tr>(t: T) -> u32 { 0 }
