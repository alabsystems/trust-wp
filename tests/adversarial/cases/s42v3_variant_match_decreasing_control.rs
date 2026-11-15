//@ expect: verify
//@ mechanism: control: a match-scoped #[variant] self-call whose decrease follows from the pattern fact y == x - 1 under x > 0
//@ fixed-by: s42 variant-recursion-scopes-v3
//@ accept-means: n/a (control)
//@ timeout: 300
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn f(x: Int) -> Int {
    pearlite! { if x > 0 { match Some(x - 1) { Some(y) => f(y) + 1, None => 0 } } else { 0 } }
}

#[ensures(f(0) == 0)]
pub fn g() {}
