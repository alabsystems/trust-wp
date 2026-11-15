//@ expect: verify
//@ mechanism: `s.holds()` at `S`, where the only definition of `holds` that applies is the BLANKET `impl<T: Marker> AssocTrait for T` (`U`'s inherent `holds` is on another type). rustc's selection picks the blanket impl at `S`, so the lookup binds it, and its `true` proves `f`.
//@ teeth: over-refusal control for D-160's applicability test: with it read back to a self-type comparison, the blanket impl is invisible, no definition applies, and `f` is refused (`unknown`); its false twin is method_call_blanket_impl_sole_candidate_false.rs.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Marker {}

pub trait AssocTrait {
    #[logic]
    fn holds(self) -> bool;
}

impl<T: Marker> AssocTrait for T {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub struct S;
impl Marker for S {}

pub struct U;
impl U {
    #[logic(open)]
    pub fn holds(self) -> bool {
        true
    }
}

#[ensures(s.holds())]
pub fn f(s: S) {}
