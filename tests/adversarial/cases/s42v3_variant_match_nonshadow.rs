//@ expect: reject
//@ verdict: error
//@ refused-with: variant `x` does not strictly decrease at self-call
//@ mechanism: a match-scoped #[variant] self-call (no parameter shadowing) carried unsupported_reason and was credited by the permissive Unsupported arm; f(1) = f(1) + 1 is inconsistent
//@ fixed-by: s42 variant-recursion-scopes-v3
//@ accept-means: a #[variant] recursion under a match arm is credited without a decrease proof again
//@ timeout: 300
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn f(x: Int) -> Int {
    pearlite! { if x > 0 { match Some(x + 1) { Some(y) => f(y - 1) + 1, None => 0 } } else { 0 } }
}

#[ensures(f(1) == 42)]
pub fn g() {}
