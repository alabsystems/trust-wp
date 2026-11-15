//@ expect: verify
//@ mechanism: a variant two modules deep, spelled with its full path (`m::n::E::C`) in
//@ mechanism: declaration order. The same guard as the re-export control, for the canonical
//@ mechanism: path form: deleting the flat-map fallback must not cost a row that the path
//@ mechanism: table already answered.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
//@ teeth: n/a — over-refusal control. `verified ✓` before and after v3.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m { pub mod n { pub enum E { C { b: u32, a: u32 }, N } } }
pub struct D { pub a: u32, pub b: u32 }

#[requires(match e { m::n::E::C { a: aa, b: _bb } => aa@ == 5, m::n::E::N => false })]
#[ensures(result@ == 5)]
pub fn g(e: m::n::E, _d: D) -> u32 { match e { m::n::E::C { b: _b, a } => a, m::n::E::N => 0 } }
