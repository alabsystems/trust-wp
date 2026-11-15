//@ expect: verify
//@ mechanism: over-refusal control for `s82v3_selfmod_path_reorder`: the SAME reordered
//@ mechanism: `self::E::C` pattern with the body returning the field the pattern really binds.
//@ mechanism: Provable only if `self::E::C` RESOLVES and is placed at its declared indices.
//@ mechanism: A driver that refuses every spelling it cannot construct textually loses this
//@ mechanism: row; a driver that reads the pattern in source order proves the wrong thing
//@ mechanism: about its twin.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
//@ teeth: n/a — over-refusal control. Measured `unknown`, exit 2 on the s82 v2 fix (the other
//@ teeth: half of the same defect: the spelling was misplaced, so the TRUE contract became
//@ teeth: unprovable while its FALSE twin verified), and `verified ✓` after v3.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E { C { b: u32, a: u32 }, N }
pub struct D { pub a: u32, pub b: u32 }

#[requires(match e { self::E::C { a: aa, b: _bb } => aa@ == 5, self::E::N => false })]
#[ensures(result@ == 5)]
pub fn g(e: E, _d: D) -> u32 { match e { E::C { b: _b, a } => a, E::N => 0 } }
