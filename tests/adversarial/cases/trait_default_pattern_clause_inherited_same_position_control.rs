//@ expect: verify
//@ mechanism: the TRUE twin of trait_default_pattern_clause_fallback_name_read_by_impl_param: the impl
//@ mechanism: overrides a trait default whose clause D-177 states over `arg2`, and destructures the
//@ mechanism: same position itself, so its own name for that parameter is `arg2` as well; the inherited
//@ mechanism: clause is kept and the impl returns the first component of that argument.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
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
    fn m(&self, x: (u32, u32), (c, _d): (u32, u32)) -> u32 { c }
}
