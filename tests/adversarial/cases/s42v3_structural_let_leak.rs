//@ expect: reject
//@ verdict: error
//@ refused-with: Recursive logic function without a #[variant] clause or a structurally decreasing argument
//@ mechanism: structural smaller_than was not scoped per let body: let t = *tl inside the Cons arm leaked into the Nil arm, where f(t, t) passes the PARAMETER t
//@ fixed-by: s42 variant-recursion-scopes-v3
//@ accept-means: a let binding leaks out of its body in the structural-recursion check again
//@ timeout: 300
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum L {
    Cons(Int, Box<L>),
    Nil,
}
use L::*;

#[logic]
pub fn f(l: L, t: L) -> Int {
    pearlite! { match l { Cons(_, tl) => { let t = *tl; 0 }, Nil => f(t, t) + 1 } }
}

#[ensures(f(Nil, Nil) == 42)]
pub fn g() {}
