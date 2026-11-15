//@ expect: reject
//@ also-verified: Tr::m
//@ mechanism: a trait method's default body destructures a parameter, and D-177 states its clause
//@ mechanism: over the parameter's positional name: `result == a` becomes `result == (arg2.0)`. An impl
//@ mechanism: that overrides the body and writes no clause inherits that text verbatim, and its body
//@ mechanism: obligation reads it by the IMPL's names; this impl spells its FIRST tuple parameter
//@ mechanism: `arg2`, so the inherited clause was stated over the wrong argument. It is the renamed-
//@ mechanism: parameter inheritance hole (an inherited clause read by the impl's parameter names, not
//@ mechanism: the trait's), reached through a name only D-177 puts in the text: the refinement check
//@ mechanism: compares positions and FAILS, so no caller is granted the clause, but the impl was
//@ mechanism: credited.
//@ accept-means: the inherited projection `arg2.0` was read on the impl's parameter `arg2`, which is
//@ accept-means: the trait's `x`.
//@ WHY THE CONTRACT IS FALSE: the trait's clause is `result == y.0`; `W.m((1, 0), (2, 3))` returns 1.
//@ WHY THE CONTRACT IS FALSE: The default body `Tr::m` is true and is credited on purpose.
//@ fixed-by: D-177 — an inherited clause that names the parameter a trait default's pattern is
//@ fixed-by: projected from is refused unless the impl gives that position the same name
//@ fixed-by: (refuse_inherited_projections_on_renamed_params); the impl discharges nothing.
//@ teeth: `<W as Tr>::m verified` beside `<W as Tr>::m trait refinement FAILED` with D-177's text
//@ teeth: rewrite and without that guard (measured on the first D-177 commit). Before D-177 the
//@ teeth: clause said `a`, which this impl does not bind, and the impl FAILED. The isolating twin
//@ teeth: trait_default_pattern_clause_inherited_same_position_control.rs verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(result == a)]
    fn m(&self, x: (u32, u32), (a, _b): (u32, u32)) -> u32 { a }
}
pub struct W;
impl Tr for W {
    fn m(&self, arg2: (u32, u32), y: (u32, u32)) -> u32 { arg2.0 }
}
