//@ expect: reject
//@ mechanism: an inner surviving-path assumption escaped its enclosing arm (unguarded premise)
//@ accept-means: f(false, true) returns with b true, so ensures(!b) is FALSE.
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: verified on e03182e2 (s29 review / s40 probe logs)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(!b)]
pub fn f(c: bool, b: bool) { if c { if b { spin() } } }
