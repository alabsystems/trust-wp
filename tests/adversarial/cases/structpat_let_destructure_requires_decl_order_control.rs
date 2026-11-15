//@ expect: verify
//@ mechanism: the over-refusal guard for the `let` lowering: a true contract whose `let`
//@ mechanism: pattern is written in DECLARATION order, the shape ordinary specifications
//@ mechanism: use. It verified under the positional lowering because written order happened
//@ mechanism: to equal declared order; it must still verify once the pattern is placed.
//@ accept-means: n/a (control).
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires({ let S { b: _bb, a: aa } = s; aa@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 { match s { S { b: _b, a } => a } }
