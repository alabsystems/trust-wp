//@ expect: verify
//@ mechanism: over-refusal control for a `type` alias — the third renaming route rustc resolves
//@ mechanism: and `def_path_str` does not produce. Declaration order, nothing reordered.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control. Verifies on campaign tip and after v2; it is here so the
//@ teeth: alias routes stay measured rather than assumed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m { pub enum E { C { a: u32, b: u32 }, N } }
pub type F = m::E;

#[requires(match e { F::C { a: aa, b: _bb } => aa@ == 5, F::N => false })]
#[ensures(result@ == 5)]
pub fn f(e: F) -> u32 { match e { m::E::C { a, b: _b } => a, m::E::N => 0 } }
