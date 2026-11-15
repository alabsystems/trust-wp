//@ expect: verify
//@ mechanism: control for closure_assertion_inherits_parent_requires_shadowed_param: the same parent and the same shadowing closure parameter, with the closure's OWN `#[requires]` saying what its assertion needs. A closure's assertion is proved under the closure's own precondition, so removing the parent fallback must not cost this.
//@ accept-means: n/a (control) — the assertion follows from the closure's own precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 7)]
#[ensures(result@ == 3)]
pub fn parent(x: u32) -> u32 {
    let c = #[requires(x@ == 3)]
    #[ensures(result@ == x@)]
    |x: u32| {
        proof_assert!(x@ == 3);
        x
    };
    c(3)
}
