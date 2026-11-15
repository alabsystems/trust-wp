//@ expect: reject
//@ mechanism: an `async` block inside an ordinary function is a coroutine body of its own. Its assertion is in neither the enclosing function's MIR nor any body `discover_proof_assert_functions` admitted, so no pass met it and the crate exited 0 around it. The enclosing function builds the future and never runs it, so ITS credit is not in question; the assertion's is.
//@ accept-means: an assertion false for every capture, in code the crate compiles, is never examined and the run is clean.
//@ WHY THE ASSERTION IS FALSE: the precondition bounds `x` below 100, so it is never 1000.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `f verified ✓` and every proof_assert counter zero.
//@ fixed-by: D-106 — coroutine bodies are discovered and their assertions refused
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
#[ensures(result@ == x@)]
pub fn f(x: u32) -> u32 {
    let _fut = async move {
        proof_assert!(x@ == 1000);
    };
    x
}
