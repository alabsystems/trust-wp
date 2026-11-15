//@ expect: verify
//@ xfail: completeness cost of s40 — a local -> ! fn whose body is not trivially inert is classified as a panic entry point even when it carries a contract, so its arm must be proved unreachable
//@ mechanism: a contracted local -> ! callee with a non-inert body (arithmetic) called under a proved precondition
//@ accept-means: n/a (control) — TRUE contracts
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 0 && x@ < 100)]
pub fn die(x: i32) -> ! { let _y = x + 1; loop {} }
#[ensures(x@ <= 0 || x@ >= 100)]
pub fn f(x: i32) { if x > 0 && x < 100 { die(x) } }
