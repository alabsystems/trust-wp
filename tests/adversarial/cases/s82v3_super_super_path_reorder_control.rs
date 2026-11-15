//@ expect: verify
//@ mechanism: over-refusal control for `s82v3_super_super_path_reorder`.
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

pub mod m { pub mod n {
    use creusot_std::prelude::*;
    #[requires(match e { super::super::E::C { a: aa, b: _bb } => aa@ == 5, super::super::E::N => false })]
    #[ensures(result@ == 5)]
    pub fn g(e: crate::E, _d: crate::D) -> u32 { match e { crate::E::C { b: _b, a } => a, crate::E::N => 0 } }
} }
