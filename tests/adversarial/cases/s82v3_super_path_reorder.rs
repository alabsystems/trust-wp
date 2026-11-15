//@ expect: reject
//@ verdict: unknown
//@ mechanism: the same defect one module deeper: `super::E::C`, written from inside a nested
//@ mechanism: module. Like `self::`, it is a path rustc resolves and `path_spellings()` cannot
//@ mechanism: produce, so the constructor table missed and the flat name->index map — taught
//@ mechanism: `a`->0, `b`->1 by the decoy struct `D` — answered for an enum variant's fields.
//@ accept-means: the spelling table's coverage, not the program's meaning, decides the
//@ accept-means: binding; every path form nobody thought to enumerate is a silent
//@ accept-means: misplacement rather than a refusal.
//@ WHY THE CONTRACT IS FALSE: the precondition constrains `a`; the body returns `b`.
//@ teeth: measured ACCEPTED, exit 0 on the s82 v2 fix. Its control verifies, and the verdict
//@ teeth: is pinned to `unknown` — the same verdict the canonical `E::C` spelling of this
//@ teeth: identical program gets.
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
    pub fn g(e: E, _d: D) -> u32 { match e { E::C { b, a: _a } => b, E::N => 0 } }
}
