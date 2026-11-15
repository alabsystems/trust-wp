//@ expect: reject
//@ mechanism: logic-fn identity — two impls of one trait logic method for u32/u64 (same solver sort Int); x.m() == y.m() for equal values (definition order ba)
//@ fixed-by: s35 logic-fn identity (type-directed receiver resolution, generic markers at call sites)
//@ accept-means: a clause was checked against a definition Rust would not select for that type
//@ teeth: accepted with exit 0 on wp-campaign fd7534d
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr { #[logic] fn m(self) -> Int; }
impl Tr for u64 { #[logic(open)] fn m(self) -> Int { pearlite!{10} } }
impl Tr for u32 { #[logic(open)] fn m(self) -> Int { pearlite!{0} } }
#[requires(x@ == y@)]
#[ensures(x.m() == y.m())]
pub fn f(x: u32, y: u64) {}
