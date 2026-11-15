//@ expect: reject
//@ verdict: error
//@ refused-with: variant `x` does not strictly decrease at self-call
//@ mechanism: match binder y then let x = y re-binding the parameter name: let substitution rewrote the argument to y - 1, which escaped the shadow check and reached the Unsupported credit
//@ fixed-by: s42 variant-recursion-scopes-v3
//@ accept-means: a let re-binding of a parameter inside a match arm hides a non-decreasing #[variant] call again
//@ timeout: 300
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn f(x: Int) -> Int {
    pearlite! { if x > 0 { match Some(x + 1) { Some(y) => { let x = y; f(x - 1) + 1 }, None => 0 } } else { 0 } }
}

#[ensures(f(1) == 42)]
pub fn g() {}
