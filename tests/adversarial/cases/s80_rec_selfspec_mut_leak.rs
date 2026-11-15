//@ expect: reject
//@ mechanism: the EMPTY self-spec must not let a `&mut` referent survive a recursive self-call; `*acc == n` is FALSE for n >= 2 because the self-call overwrites it
//@ accept-means: the in-function `proof_assert` lane carried the pre-call assignment `*acc = n` across the self-call instead of havocking the referent
//@ fixed-by: n/a — s80 shape gate
//@ teeth: DOCUMENTATION PLUS A LIVE FINDING, NOT A GATE THIS FRONT CLOSED. Measured byte-identically at 1bca2b5f (pre-fix) and 0bead8ec (post-fix): the CRATE is rejected (exit 2 — the item is withheld on an unwalked arithmetic panic site) but `trust-wp: proof_assert in creusot_test::rec_set verified ✓` credits the FALSE claim on BOTH (probe p12). The lane is not vacuous — probe p14 answers `unknown` to `*acc == 12345u32` on both sides — so this is a live pre-existing proof_assert-lane defect, handed on by s80 and owned by nobody yet. The assertion credit is deliberately NOT declared in `also-verified-assertion`, so this case is RED on it until the proof_assert lane havocs the referent across the self-call; the crate-level rejection does not excuse it.
//@ also-verified: rec_set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n)]
pub fn rec_set(n: u32, acc: &mut u32) {
    if n > 0 {
        *acc = n;
        rec_set(n - 1, acc);
        // FALSE for n >= 2: the self-call leaves `*acc == 1`.
        proof_assert!(*acc == n@);
    }
}
