//@ expect: verify
//@ mechanism: the over-refusal half of the named-literal arm. `mk` writes `a: p, b: q`, so
//@ mechanism: `mk(x, y).a` is `x == 5` and the postcondition is TRUE under the declared
//@ mechanism: reading. Under the source-order reading `a` receives `q == 0` and this is NOT
//@ mechanism: provable — which is what it MEASURED on the pre-s82 campaign tip 7bf6aabb:
//@ mechanism: failed, exit 1. On the s82 v4 head: ACCEPTED, exit 0.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub b: u32,
    pub a: u32,
}

#[logic(open)]
pub fn mk(p: u32, q: u32) -> S {
    pearlite! { S { a: p, b: q } }
}

#[requires(x@ == 5 && y@ == 0)]
#[ensures(mk(x, y).a@ == 5)]
pub fn f(s: S, x: u32, y: u32) -> u32 {
    s.a
}
