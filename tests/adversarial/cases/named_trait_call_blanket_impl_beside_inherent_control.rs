//@ expect: verify
//@ mechanism: isolating twin of named_trait_call_blanket_impl_inherent_shadow with the two bodies swapped: the blanket `AssocTrait::holds` is `true` and the inherent `S::holds` is `false`, so `AssocTrait::holds(s)` holds and a call bound to the inherent method would fail. The named trait narrows the lookup to its own declaration and implementations, where the blanket impl is the one rustc's selection picks at `S`.
//@ teeth: over-refusal control for D-160's named-trait narrowing: its false twin is refused (`unknown`) with the narrowing knocked out, the lookup then seeing the blanket and the inherent method as two candidates.
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
impl S {
    #[logic(open)]
    pub fn holds(self) -> bool {
        false
    }
}

#[ensures(AssocTrait::holds(s))]
pub fn f(s: S) {}
