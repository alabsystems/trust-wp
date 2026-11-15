//@ expect: reject
//@ mechanism: logic-fn identity — impls for u32/u64; receiver-style call on the u64 receiver (definition order ba)
//@ fixed-by: s35 logic-fn identity (type-directed receiver resolution, generic markers at call sites)
//@ accept-means: a clause was checked against a definition Rust would not select for that type
//@ teeth: rejected on fd7534d only in this definition order; its twin order was accepted (see s35 progress.md)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr { #[logic] fn m(self) -> Int; }
impl Tr for u64 { #[logic(open)] fn m(self) -> Int { pearlite!{10} } }
impl Tr for u32 { #[logic(open)] fn m(self) -> Int { pearlite!{0} } }
#[ensures(result@ == x.m())]
pub fn f(x: u64) -> u32 { 0 }
