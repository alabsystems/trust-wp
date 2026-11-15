//@ expect: verify
//@ mechanism: nested spin arms: the guarded returning-path fact c ==> !b premises the postcondition
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(!(c && b))]
pub fn f(c: bool, b: bool) { if c { if b { spin() } } }
