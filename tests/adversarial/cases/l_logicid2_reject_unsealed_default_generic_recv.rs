//@ expect: reject
//@ mechanism: logic-fn identity v2 — an UNSEALED default body is a fact about no `Self`: an impl may override it, so it must not bind on an abstract generic receiver
//@ fixed-by: s35 logic-fn identity v2 (only a sealed declaration body binds for a bound generic parameter)
//@ accept-means: the trait's default body answered `x.g()` at an unknown `Self`, although `<A as Tr>::g` is false
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Tr {
    #[logic(open)]
    fn g(self) -> bool {
        true
    }
}
pub struct A;
impl Tr for A {
    #[logic(open)]
    fn g(self) -> bool {
        false
    }
}
#[ensures(x.g())]
pub fn p<T: Tr>(x: T) {}
