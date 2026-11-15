//@ expect: verify
//@ mechanism: a contracted -> ! spin callee whose precondition the caller arm proves; continuation unreachable
//@ accept-means: n/a (control) — TRUE contracts, must keep verifying
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(b)]
pub fn die(b: bool) -> ! { loop {} }
#[ensures(!b)]
pub fn f(b: bool) { if b { die(b) } }
