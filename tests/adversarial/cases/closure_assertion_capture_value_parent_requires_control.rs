//@ expect: verify
//@ xfail: the price of D-106, named. The assertion is TRUE — `x` is captured unchanged from the parameter the parent's `#[requires]` pins — but only the PARENT knows it. The closure's own environment models no value of a capture at construction: its contract lane refutes `#[ensures(result@ == 7)]` on the same closure, and Creusot's closure VC has no such premise either, so the assertion now fails where it used to verify on the parent's entry fact. It differs from closure_assertion_inherits_parent_entry_requires_after_overwrite only in the `x = 3` overwrite, which is exactly the difference the parent's entry fact could not see.
//@ mechanism: over-refusal control for the removed typeck-root fallback: a true assertion about a captured value that only the enclosing function's precondition establishes
//@ fixed-by: n/a (open incompleteness; closes when a closure's lane models the values its captures take at construction, for every construction site)
//@ accept-means: n/a (control) — this assertion is TRUE; an XPASS means the closure's own lane learned the capture's value.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 7)]
pub fn parent(x: u32) {
    let c = #[ensures(true)]
    move || {
        proof_assert!(x@ == 7);
    };
    c()
}
