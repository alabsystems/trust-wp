//@ expect: reject
//@ mechanism: the surviving-path assumption x <= 0 discharged the -> ! callee precondition on the diverging arm
//@ accept-means: f(1) calls die(1) although die requires x > 5. FALSE.
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: verified on e03182e2 (s29 review / s40 probe logs)
//@ also-verified: die
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 5)]
pub fn die(x: i32) -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32) { if x > 0 { die(x) } }
