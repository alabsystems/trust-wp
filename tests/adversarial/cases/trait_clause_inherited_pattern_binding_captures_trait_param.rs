//@ expect: reject
//@ fn-failed: <W as Tr>::m
//@ mechanism: an impl method with no clause of its own is verified against its trait method's
//@ mechanism: clause, whose names are the TRAIT's parameters. The impl's own body was then read
//@ mechanism: through its parameter-destructuring substitutions (extract_param_destructuring_substitutions:
//@ mechanism: every name a pattern parameter binds, mapped to its projection), and those were applied to
//@ mechanism: `requires`/`ensures` as well as to the loop clauses. The impl's pattern binding `pq`
//@ mechanism: therefore replaced the trait's parameter `pq`, and the impl was credited on a clause that
//@ mechanism: speaks of its second argument.
//@ accept-means: the inherited `result == pq` was read as the impl's pattern binding `pq` (the first
//@ accept-means: component of the SECOND argument) instead of the trait's parameter `pq` (the first).
//@ WHY THE CONTRACT IS FALSE: `W.m(1, (2, 3))` returns 2; the trait's clause says `result == 1`.
//@ fixed-by: D-177 — `requires`/`ensures` name a pattern binding as its parameter projection in the
//@ fixed-by: text every reader shares, and the owner's MIR substitutions reach only the loop clauses.
//@ teeth: `<W as Tr>::m verified` at the base (the crates before D-177, checked out in place), and
//@ teeth: not FAILED with the D-177 text rewrite alone; the isolating twin
//@ teeth: trait_clause_inherited_pattern_binding_same_names_control.rs verifies on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(result == pq)]
    fn m(&self, pq: u32, other: (u32, u32)) -> u32;
}
pub struct W;
impl Tr for W {
    fn m(&self, _x: u32, (pq, _b): (u32, u32)) -> u32 { pq }
}
