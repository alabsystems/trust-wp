//@ expect: verify
//@ mechanism: the unshadowed twin of proof_assert_shadowed_param_receiver_beside_same_typed_receiver.rs: `f(x: A, y: A)` asserts `x.holds() && y.holds()` with no `let x`, so the assertion's `x` is the parameter. rustc types both receivers `A` and resolves both calls to `A::holds`, which is what the lookup reads: the root rule confirms it.
//@ teeth: over-refusal control for D-163's receiver-root rule: a rule that refused every receiver rooted at a parameter, or matched roots by anything but the variable, turns this `unknown`.
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

pub fn f(x: A, y: A) {
    proof_assert!(x.holds() && y.holds());
}
