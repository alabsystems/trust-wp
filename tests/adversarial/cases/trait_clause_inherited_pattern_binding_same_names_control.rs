//@ expect: verify
//@ mechanism: the TRUE twin of trait_clause_inherited_pattern_binding_captures_trait_param: the impl
//@ mechanism: still destructures its second argument, but names its first parameter `pq` as the trait
//@ mechanism: does and returns it, so the inherited `result == pq` holds of it.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
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
    fn m(&self, pq: u32, (c, _b): (u32, u32)) -> u32 { pq }
}
