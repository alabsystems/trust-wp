//@ expect: reject
//@ mechanism: logic-fn identity — `A::k()` with a same-named inherent `k` in `impl B` (definition order ab)
//@ fixed-by: s35 logic-fn identity (unique ids + owner-scope resolution + receiver dispatch)
//@ accept-means: a clause was checked against another definition that shares the short name
//@ teeth: accepted with exit 0 on wp-campaign fd7534d in at least one definition order (see s35 progress.md)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
pub struct B;
impl A {
    #[logic(open)] pub fn k() -> Int { pearlite!{0} }
}
impl B {
    #[logic(open)] pub fn k() -> Int { pearlite!{10} }
}
#[ensures(result@ == A::k())]
pub fn f() -> u32 { 10 }
