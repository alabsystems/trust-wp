//@ expect: verify
//@ xfail: pre-existing over-refusal (f FAILED, ay_result=trust-wp-structural-provenance) on e03182e2 and after s40; not a diverging-callee lane
//@ mechanism: contract-free non -> ! callee whose assert holds at the call site h(1)
//@ accept-means: n/a (control) — TRUE contract
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn h(x: i32) { assert!(x > 0) }
#[ensures(true)]
pub fn f() { h(1) }
