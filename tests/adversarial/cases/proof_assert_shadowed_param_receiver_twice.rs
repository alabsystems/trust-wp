//@ expect: reject
//@ mechanism: `f(x: A)` asserts `x.holds()`, shadows `x` with `let x = B;`, and asserts the same text again. Both assertions carry one tag (kind and text), so their type-check bodies are read together. The receiver lookup reads both `x` as the parameter's `A` (`Resolver::receiver_type` reads the signature's binding first) and binds `A::holds`; matched by receiver type, the first assertion's `x.holds()` (an `A`) confirmed it for the second, whose `x` is `B`.
//@ accept-means: an assertion about a shadowing local was confirmed by another assertion of the same text about the parameter it shadows.
//@ WHY IT IS FALSE: the second assertion's `x` is `B` and `B::holds` is `false`; Creusot's goal for it is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (both `proof_assert in creusot_test::f verified ✓`) before the confirmation matched receivers by the variable they are rooted at. Rejected with the root rule: rustc typed the calls on `x` as `A` and as `B`, so the lookup's `A` is not rustc's typing of `x` and both assertions' calls are refused (the first one's price: its body, read alone, would confirm it).
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

pub fn f(x: A) {
    proof_assert!(x.holds());
    let x = B;
    proof_assert!(x.holds());
}
