//@ expect: reject
//@ mechanism: a `proof_assert!` in a nested block of `host` names `k()`, and that block declares a
//@ mechanism: logic function `k` (0); the crate root declares another (10). Rust resolves the
//@ mechanism: assertion's `k` in the block where it is written. The resolver resolves an assertion in
//@ mechanism: the scope of its containing function, and that scope is the function's MODULE, so it
//@ mechanism: reads the root's `k` and `k() == 10`, false of the block's `k`, is credited.
//@ fixed-by: D-195 — REFUSED, not resolved: `k` is declared in a nested block of the owner's body,
//@ fixed-by: visible at some positions of a body clause and not at others, and the assertion's position
//@ fixed-by: is not read (`block_scope::own_body_binding`), so the call is left unresolved and the
//@ fixed-by: encoder refuses the clause.
//@ accept-means: the assertion `k() == 10` with the block's `k` (0) is credited, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`proof_assert in creusot_test::host verified ✓`). With D-195:
//@ teeth: `unknown` (`proof_assert in creusot_test::host error: ... `k` names one of several
//@ teeth: definitions`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub fn host() -> u32 {
    {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
        proof_assert!(k() == 10);
    }
    0
}
