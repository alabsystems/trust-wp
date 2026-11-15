//@ expect: reject
//@ mechanism: the surviving-path condition was pushed as an assumption and discharged an obligation emitted BEFORE the switch
//@ accept-means: need(b) requires !b but f(true) calls need(true). FALSE.
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
pub fn f(b: bool) { need(b); if b { spin() } }
