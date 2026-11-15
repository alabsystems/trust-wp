//@ expect: verify
//@ mechanism: over-refusal control — the decreasing twin of `s80_contractless_recursive_nondecreasing`; a contract-less recursive function with a genuinely decreasing variant must verify
//@ teeth: n/a — over-refusal control. This is the same shape as the three blocked e2e tests (termination_project::recursive_countdown). REJECTED at 1bca2b5f with `violated ensures #1: (!(n <= 0) ==> false)` at the degenerate `n = 1`; VERIFIED at 0bead8ec.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n)]
pub fn rec_down(n: i32) -> i32 {
    if n <= 0 { 0 } else { rec_down(n - 1) }
}
