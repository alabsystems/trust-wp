//@ expect: verify
//@ mechanism: over-refusal control for `s82v3_super_path_reorder` — the same `super::E::C`
//@ mechanism: pattern with the body returning the field it really binds.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
//@ teeth: n/a — over-refusal control. Measured `unknown`, exit 2 on the s82 v2 fix while its
//@ teeth: FALSE twin verified; `verified ✓` after v3.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E { C { b: u32, a: u32 }, N }
pub struct D { pub a: u32, pub b: u32 }

pub mod inner {
    use super::{D, E};
    use creusot_std::prelude::*;
    #[requires(match e { super::E::C { a: aa, b: _bb } => aa@ == 5, super::E::N => false })]
    #[ensures(result@ == 5)]
    pub fn g(e: E, _d: D) -> u32 { match e { E::C { b: _b, a } => a, E::N => 0 } }
}
