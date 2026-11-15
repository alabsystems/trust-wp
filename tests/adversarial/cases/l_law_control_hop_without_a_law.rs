//@ expect: verify
//@ mechanism: the same abstract-receiver hop with NO law on the trait — the postcondition is entailed by the precondition alone, so neutralizing unproved laws must not refuse it
//@ accept-means: n/a (control): a hop that never needed the law must keep verifying
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Spec {
    #[logic]
    fn base(self) -> Int;
    #[logic]
    fn bumped(self) -> Int;
}
impl Spec for i32 {
    #[logic(open)]
    fn base(self) -> Int { pearlite! { self@ } }
    #[logic(open)]
    fn bumped(self) -> Int { pearlite! { self@ } }
}
#[requires(v@ == t.bumped())]
#[ensures(result@ == t.bumped())]
pub fn hop<T: Spec>(t: T, v: i32) -> i32 { v }
