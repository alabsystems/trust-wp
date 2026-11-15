//@ expect: verify
//@ mechanism: over-refusal control for contract_free_terminates_overflow_uncharged: the SAME
//@ mechanism: clause-free `#[check(terminates)]` host with its addition guarded by `a < 10`. It is
//@ mechanism: extracted only because the extraction gate now reads its overflow assert, and it
//@ mechanism: verifies, so the gate charges the goal rather than refusing marker-bearing bodies.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `hop verified ✓`, exit 0; the unguarded twin is refuted (D-95).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

#[check(terminates)]
pub fn hop(a: u32) -> u32 {
    if a < 10 { a + 1 } else { 0 }
}
