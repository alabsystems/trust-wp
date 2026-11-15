//@ expect: reject
//@ verdict: failed
//@ fn-failed: boom
//@ mechanism: the same uncharged abort obligation as `contract_free_assert_uncharged`, with no
//@ mechanism: contracted item beside it. Before the fix the crate examined nothing and exited 2,
//@ mechanism: which is a refusal rather than a refutation: the pair separates "trust-wp had
//@ mechanism: nothing to say" from "trust-wp refuted it".
//@ accept-means: a body that panics on a reachable input was examined by nobody
//@ fixed-by: the contract-free abort/callee-precondition discovery pass
//@ teeth: verified — exit 2 (nothing examined) on this branch's parent commit, `boom FAILED` after
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// `boom(0)` panics.
pub fn boom(a: u32) {
    assert!(a == 1);
}
