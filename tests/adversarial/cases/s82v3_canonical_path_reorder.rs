//@ expect: reject
//@ verdict: unknown
//@ mechanism: the SPELLING-axis control for the three cases above: the identical program,
//@ mechanism: decoy struct and all, spelled `E::C` — the one form `path_spellings()` does
//@ mechanism: produce. It rejected throughout, which is what made the others a defect in the
//@ mechanism: lookup rather than in the pattern: same program, one token apart, opposite
//@ mechanism: verdicts.
//@ accept-means: the defect would have moved into the canonical path too, i.e. the placement
//@ accept-means: broke everywhere rather than only where the table missed.
//@ WHY THE CONTRACT IS FALSE: the precondition constrains `a`; the body returns `b`.
//@ teeth: pinned to `unknown`, the verdict its three re-spelled twins must also reach. A case
//@ teeth: that is green on every spelling proves nothing; this one exists to be compared.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E { C { b: u32, a: u32 }, N }
pub struct D { pub a: u32, pub b: u32 }

#[requires(match e { E::C { a: aa, b: _bb } => aa@ == 5, E::N => false })]
#[ensures(result@ == 5)]
pub fn g(e: E, _d: D) -> u32 { match e { E::C { b, a: _a } => b, E::N => 0 } }
