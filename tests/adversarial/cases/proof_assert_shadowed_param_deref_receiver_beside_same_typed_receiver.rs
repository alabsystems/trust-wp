//@ expect: reject
//@ mechanism: the dereference spelling of proof_assert_shadowed_param_receiver_beside_same_typed_receiver.rs:
//@ mechanism: `f(x: &A, y: A)` shadows `x` with `let x = &B;` and asserts `(*x).holds() && y.holds()`. The
//@ mechanism: receiver lookup reads `*x` at the parameter's type (`Resolver::receiver_type` peels the
//@ mechanism: dereference and reads the signature's binding first), `A`, and binds `A::holds`. Matched by
//@ mechanism: receiver type alone, `y.holds()` (an `A`, resolved to `A::holds`) confirms it; the root rule
//@ mechanism: reads the call's receiver through `*` to the variable `x`, which rustc typed `&B`.
//@ accept-means: an assertion about a shadowing local, read through a dereference, was read at the shadowed parameter's type and proved.
//@ WHY IT IS FALSE: `x` is `&B` where the assertion is written and `B::holds` is `false`, so the assertion is `false`.
//@ teeth: MEASURED ACCEPTED, exit 0 (`proof_assert in creusot_test::f verified ✓`) at the campaign tip, and with
//@ teeth: D-163's confirmation built to match by receiver type alone (the root knocked out); rejected (`unknown`)
//@ teeth: with the root rule.
//@ fixed-by: D-163 — a receiver rooted at a variable is confirmed only against rustc's calls on that variable, each typed as the lookup typed it.
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
    let x = &B;
    proof_assert!((*x).holds() && y.holds());
}
