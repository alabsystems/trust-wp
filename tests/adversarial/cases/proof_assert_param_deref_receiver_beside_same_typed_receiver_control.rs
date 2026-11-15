//@ expect: verify
//@ mechanism: the unshadowed twin of proof_assert_shadowed_param_deref_receiver_beside_same_typed_receiver.rs:
//@ mechanism: `f(x: &A, y: A)` asserts `(*x).holds() && y.holds()` with no `let x`, so rustc reads both calls
//@ mechanism: as `A::holds`, the lookup's reading: the root rule confirms it through the dereference.
//@ teeth: over-refusal control for D-163's receiver-root rule read through `*`: MEASURED verified at the campaign tip, with the root rule, and with the root knocked out (matching by type alone); a root rule that did not read rustc's receiver through the dereference would leave no call rooted at `x` and turn it `unknown`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A;
pub struct B;

impl A {
    #[logic(open)]
    pub fn holds(self) -> bool {
        true
    }
}

impl B {
    #[logic(open)]
    pub fn holds(self) -> bool {
        false
    }
}

pub fn f(x: &A, y: A) {
    proof_assert!((*x).holds() && y.holds());
}
