//@ expect: reject
//@ mechanism: an inner surviving-path assumption from the then arm discharged an obligation in the else arm
//@ accept-means: f(false, true) calls need(true) although need requires !b. FALSE.
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: verified on e03182e2 (s29 review / s40 probe logs)
//@ also-verified: need
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(!b)]
pub fn need(b: bool) {}
pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(c: bool, b: bool) { if c { if b { spin() } } else { need(b) } }
