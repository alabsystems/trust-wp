//@ expect: reject
//@ also-verified: Tr::m
//@ mechanism: a trait method's default body destructures a parameter (`(a, _b)`) and its clause
//@ mechanism: names the binding `a`. An impl that overrides the body and writes no clause inherits the
//@ mechanism: clause text verbatim, and the impl's body obligation reads it by the IMPL's names: the
//@ mechanism: impl calls its FIRST parameter `a`, so the inherited `result == a` was stated over it.
//@ accept-means: the inherited clause's pattern binding `a` was read as the impl's parameter `a`.
//@ WHY THE CONTRACT IS FALSE: the trait's clause is `result == y.0`; `W.m(1, (2, 3))` returns 1.
//@ WHY THE CONTRACT IS FALSE: The default body `Tr::m` is true and is credited on purpose.
//@ fixed-by: D-177 — the trait's clause names the binding as its parameter projection, `(__twp_arg2.0)`,
//@ fixed-by: and an impl that names position 2 otherwise does not inherit a clause over `__twp_arg2`
//@ fixed-by: (refuse_inherited_projections_on_renamed_params). The same capture through a parameter
//@ fixed-by: that spells the fallback name is trait_default_pattern_clause_fallback_name_read_by_impl_param.
//@ teeth: `<W as Tr>::m verified` at the base (the crates before D-177, checked out in place).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait Tr {
    #[ensures(result == a)]
    fn m(&self, x: u32, (a, _b): (u32, u32)) -> u32 { a }
}
pub struct W;
impl Tr for W {
    fn m(&self, a: u32, y: (u32, u32)) -> u32 { a }
}
