//@ expect: verify
//@ mechanism: over-refusal guard for the `..` rest-pattern path: a rest pattern naming the FIRST
//@ mechanism: declared field, which is what the positional reading already gets right. It must
//@ mechanism: keep verifying after the rest path learns to refuse what it cannot place.
//@ accept-means: n/a (control).
//@ teeth: n/a — over-refusal control; verifies on main.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub enum V { C { a: u32, b: u32 }, N }
#[requires(match v { V::C { a: aa, .. } => aa@ == 5, V::N => false })]
#[ensures(result@ == 5)]
pub fn f(v: V) -> u32 { match v { V::C { a, b: _b } => a, V::N => 0 } }
