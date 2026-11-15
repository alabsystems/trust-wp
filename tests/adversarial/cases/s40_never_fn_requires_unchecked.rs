//@ expect: reject
//@ mechanism: the surviving-path treatment dropped the whole -> ! arm, including the callee precondition obligation
//@ accept-means: die's precondition x > 0 was not checked at f(0). FALSE.
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: verified on e03182e2 (s29 review / s40 probe logs)
//@ also-verified: die
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 0)]
#[ensures(true)]
pub fn die(x: i32) -> ! { loop {} }
#[ensures(true)]
pub fn f(x: i32) { if x <= 0 { die(x) } }
