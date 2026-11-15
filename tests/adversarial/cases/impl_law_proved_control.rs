//@ expect: verify
//@ mechanism: a concrete impl's law is proved like any logic function (Creusot's `vc_nonneg` for the impl), where it used to be exposed without a proof attempt; its refinement reads the trait's `a.v()` at `bool`, the same definition the impl's clause names
//@ teeth: over-refusal control — measured `law postcondition unverified (non-strict axiom exposure)` before laws were proved, then a scope-dependent refinement error on `.v(..)` before method calls were resolved; `<bool as Tr>::nonneg verified ✓` and its refinement verified, exit 0, after both. Its twin `impl_law_false` is never credited
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn v(self) -> Int;
    #[logic(law)]
    #[ensures(a.v() >= 0)]
    fn nonneg(a: Self);
}

impl Tr for bool {
    #[logic(open)]
    fn v(self) -> Int {
        if self { 1 } else { 0 }
    }
    #[logic(open, law)]
    #[ensures(a.v() >= 0)]
    fn nonneg(a: Self) {}
}
