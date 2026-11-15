//@ expect: verify
//@ mechanism: over-refusal control for the PLAIN STRUCT arm: a reordered struct pattern whose
//@ mechanism: contract is TRUE. The struct field map already resolves this today; it must keep
//@ mechanism: resolving it after the enum arm and the fail-closed refusal land.
//@ accept-means: n/a (control).
//@ teeth: n/a — over-refusal control; verifies on main.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S5 { pub a: u32, pub b: u32 }
#[requires(s.a@ == 5 && s.b@ == 7)]
#[ensures(match s { S5 { b: bb, a: aa } => aa@ == 5 && bb@ == 7 })]
pub fn g(s: S5) {}
