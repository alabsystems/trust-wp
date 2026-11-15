//@ expect: verify
//@ mechanism: over-refusal control for `s82v2_alias_reorder`: same renamed-import pattern, body
//@ mechanism: returns the field the pattern really binds.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
//@ teeth: n/a — over-refusal control. Measured refused on the s82 v1 fix (`no declaration for
//@ teeth: `F::C` was found`) and verified on campaign tip and after v2.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m { pub enum E { C { b: u32, a: u32 }, N } }
use m::E as F;

#[requires(match e { F::C { a: aa, b: _bb } => aa@ == 1, F::N => false })]
#[ensures(result@ == 1)]
pub fn g(e: F) -> u32 { match e { m::E::C { b: _b, a } => a, m::E::N => 0 } }
