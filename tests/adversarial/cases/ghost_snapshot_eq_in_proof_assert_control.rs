//@ expect: verify
//@ mechanism: the TRUE twin of ghost_snapshot_eq_in_program_context_always_true: the same comparison
//@ mechanism: stated in a `proof_assert!`, where `==` is the logical equality and nothing runs.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified`, exit 0, when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f() {
    let a = snapshot!(1i32);
    let b = snapshot!(2i32);
    proof_assert!(a != b);
    proof_assert!(*a == 1i32);
}
