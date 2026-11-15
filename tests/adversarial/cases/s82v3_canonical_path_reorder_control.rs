//@ expect: verify
//@ mechanism: over-refusal control for `s82v3_canonical_path_reorder` — the declaration-order
//@ mechanism: reading of the same reordered pattern, spelled canonically.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
//@ teeth: n/a — over-refusal control. `verified ✓` throughout; it is the baseline the
//@ teeth: re-spelled controls are compared against.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E { C { b: u32, a: u32 }, N }
pub struct D { pub a: u32, pub b: u32 }

#[requires(match e { E::C { a: aa, b: _bb } => aa@ == 5, E::N => false })]
#[ensures(result@ == 5)]
pub fn g(e: E, _d: D) -> u32 { match e { E::C { b: _b, a } => a, E::N => 0 } }
