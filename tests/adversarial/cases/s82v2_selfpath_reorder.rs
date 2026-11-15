//@ expect: reject
//@ mechanism: the s82 field-order defect spelled `Self::`, inside the enum's own impl. `E::C`
//@ mechanism: declares `{b, a}`; the pattern writes `{a, b}`. Both fields are u32, so nothing
//@ mechanism: mistypes — the precondition simply constrains the WRONG field.
//@ accept-means: a `Self::`-qualified pattern is placed in the order it was WRITTEN, so a
//@ accept-means: precondition attaches to a field other than the one it names.
//@ WHY THE CONTRACT IS FALSE: the precondition pins `a`, the body returns `b`, and
//@ WHY THE CONTRACT IS FALSE: `E::C { b: 0, a: 1 }.get()` returns 0.
//@ teeth: its control `s82v2_selfpath_reorder_control` is the SAME pattern with the body
//@ teeth: returning `a` instead, and that one verifies — so the pair shows the placement is
//@ teeth: DECLARATION order rather than a blanket refusal of `Self::`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E { C { b: u32, a: u32 }, N }

impl E {
    #[requires(match self { Self::C { a: aa, b: _bb } => aa@ == 1, Self::N => false })]
    #[ensures(result@ == 1)]
    pub fn get(self) -> u32 { match self { E::C { b, a: _a } => b, E::N => 0 } }
}
