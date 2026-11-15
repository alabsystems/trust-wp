//@ expect: reject
//@ mechanism: `f(x: A, y: A)` shadows `x` with `let x = B;` and then asserts `x.holds() && y.holds()`. Rust reads the assertion's `x` as the local, so `x.holds()` is `B::holds`. The receiver lookup types a name the owner's signature binds from the signature (`Resolver::receiver_type` reads `bound` before the body's locals), so it reads `x` as `A` and binds `A::holds`. D-163's confirmation matched the lookup's call against rustc's by receiver TYPE, and `y.holds()` has type `A` and resolves to `A::holds`, so it confirmed the misreading.
//@ accept-means: an assertion about a shadowing local was read at the shadowed parameter's type and proved.
//@ WHY IT IS FALSE: `x` is `B` where the assertion is written and `B::holds` is `false`, so the assertion is `false`; Creusot's goal for it is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (`proof_assert in creusot_test::f verified ✓`) before the confirmation matched receivers by the variable they are rooted at; the lookup's reading predates D-163, which confirmed it. Rejected with the root rule: rustc typed the assertion's `x` as `B`, not the lookup's `A`, and the call is refused.
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

pub fn f(x: A, y: A) {
    let x = B;
    proof_assert!(x.holds() && y.holds());
}
