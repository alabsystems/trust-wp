//@ expect: reject
//@ mechanism: a CONTRACT-FREE fn whose `assert!` can fail. Creusot emits `Terminator::Abort`
//@ mechanism: (`<bb> = {false} any`) on the assert's failing arm and must prove it unreachable.
//@ mechanism: trust-wp made a function a verification target only for a contract clause, a
//@ mechanism: proof_assert, a trait origin or an arithmetic panic site, so this body was a target
//@ mechanism: of NOTHING: its abort obligation was stated in no run, and the crate exited 0 on the
//@ mechanism: strength of `anchor` alone.
//@ accept-means: a body that panics on a reachable input was examined by nobody and the crate still
//@ accept-means: reported a clean verification run
//@ fixed-by: the contract-free abort/callee-precondition discovery pass
//@ teeth: verified — ACCEPTED on this branch's parent commit, rejected after the pass lands
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// The crate needs one item that verifies, or the run exits 2 (nothing proved)
// and the missing obligation hides behind the refusal instead of behind a pass.
#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// `boom(0)` panics.
pub fn boom(a: u32) {
    assert!(a == 1);
}
