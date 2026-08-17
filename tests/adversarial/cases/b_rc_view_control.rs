//@ expect: verify
//@ mechanism: Rc/Arc view-sort hijack — the premise-fabrication (over-refusal) direction
//@ fixed-by: 197ed3e (peel Rc/Arc in ADT collection); latent on main before it via
//@ fixed-by: per_contract.rs / prep.rs threading unfiltered decls into every contract scope
//@ accept-means: n/a (control). This is THE case with teeth for the hijack: the defect's
//@ accept-means: direction is premise WEAKENING, which can never make a false goal provable — it
//@ accept-means: makes a TRUE goal unprovable. Rejecting this control reproduces the adjudicated
//@ accept-means: arc_and_rc counterexample (rc and rc3 collapsed to the same value).
//@
//@ The proof needs both view premises: distinct contents imply distinct allocations, so
//@ `!Rc::ptr_eq(&a, &b)` holds. Fabricate `a@ == 0` / `b@ == 1` away and nothing distinguishes
//@ them, so the solver is free to merge them and the assertion fails with a model-validated
//@ counterexample (memory/adtpa-ce-adjudication.md).
//@ teeth: ★VERIFIED. Method (ii): both halves of 197ed3e disabled in-tree, A/B'd in one build.
//@ teeth: Result: REJECTED with a counterexample — the adjudicated arc_and_rc failure reproduces
//@ teeth: (memory/adtpa-ce-adjudication.md: rc and rc3 collapse to the same value).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use ::std::rc::Rc;
use creusot_std::prelude::*;

pub fn rc_distinct_contents_distinct_pointers() {
    let a = Rc::new(0i32);
    let b = Rc::new(1i32);
    proof_assert!(*a@ == 0i32);
    proof_assert!(*b@ == 1i32);
    let same = Rc::ptr_eq(&a, &b);
    proof_assert!(!same);
}
