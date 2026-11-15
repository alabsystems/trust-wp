//@ expect: reject
//@ mechanism: the s82 field-order defect reached through a RENAMED IMPORT. `m::E::C` declares
//@ mechanism: `{b, a}` and the contract spells the type `F`, a name `def_path_str` never
//@ mechanism: produces. Both fields are u32, so the precondition simply constrains the wrong one.
//@ accept-means: a pattern spelled through an alias is placed in the order it was WRITTEN.
//@ WHY THE CONTRACT IS FALSE: the precondition pins `a`, the body returns `b`, and
//@ WHY THE CONTRACT IS FALSE: `g(F::C { b: 0, a: 1 })` returns 0.
//@ teeth: its control `s82v2_alias_reorder_control` is the same pattern with the body returning
//@ teeth: `a`, and verifies — so the alias RESOLVES rather than being refused wholesale.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m { pub enum E { C { b: u32, a: u32 }, N } }
use m::E as F;

#[requires(match e { F::C { a: aa, b: _bb } => aa@ == 1, F::N => false })]
#[ensures(result@ == 1)]
pub fn g(e: F) -> u32 { match e { m::E::C { b, a: _a } => b, m::E::N => 0 } }
