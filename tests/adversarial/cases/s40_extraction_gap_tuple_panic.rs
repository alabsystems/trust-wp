//@ expect: reject
//@ mechanism: context extraction failed ('failed to classify integer SwitchInt discriminant' on a tuple match) before the panic arm was walked; the empty extraction was credited verified
//@ accept-means: a reachable panic!() was never turned into an obligation. FALSE: f((true, true)) panics.
//@ fixed-by: wp-s40 diverging-callees (extraction fail-closed demotion)
//@ teeth: verified on the s40 WIP tree before the demotion (probe f07)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(p: (bool, bool)) { match p { (true, true) => panic!(), _ => {} } }
