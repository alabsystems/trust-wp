//@ expect: verify
//@ mechanism: over-refusal control for `s82v2_selfpath_reorder`: the SAME reordered `Self::C`
//@ mechanism: pattern with the body returning the field the pattern really binds. Provable only
//@ mechanism: if `Self::C` RESOLVES and is placed at its declared indices — a driver that
//@ mechanism: refuses every `Self::`-qualified pattern loses this row, and a driver that reads
//@ mechanism: the pattern in source order proves the wrong thing about it.
//@ accept-means: n/a (control) — this contract is TRUE under the correct binding.
//@ teeth: n/a — over-refusal control. Measured `error: ... no declaration for `Self::C` was
//@ teeth: found` on the s82 v1 fix, and `verified ✓` on campaign tip and after v2.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E { C { b: u32, a: u32 }, N }

impl E {
    #[requires(match self { Self::C { a: aa, b: _bb } => aa@ == 1, Self::N => false })]
    #[ensures(result@ == 1)]
    pub fn get(self) -> u32 { match self { E::C { b: _b, a } => a, E::N => 0 } }
}
