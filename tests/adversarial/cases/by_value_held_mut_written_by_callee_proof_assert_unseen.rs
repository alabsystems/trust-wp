//@ expect: reject
//@ mechanism: the proof_assert lane's spelling of by_value_held_mut_written_by_callee_unseen:
//@ mechanism: `put(Some(&mut c))` writes 5 through the `Option`-held borrow, and the substitution walk
//@ mechanism: gives `c` no post-call value.
//@ accept-means: a `proof_assert!` is credited although the callee has set the asserted local to 5.
//@ WHY THE CONTRACT IS FALSE: at the assertion `c` is 5.
//@ fixed-by: D-129: a proof_assert reads no local a holder of its borrow may have written; the call
//@ fixed-by: handed `Some(&mut c)` is such a write, so the read of `c` is refused as stale.
//@ teeth: MEASURED as ACCEPTED, `proof_assert in creusot_test::host verified`, with and without
//@ teeth: D-140 on a tree without D-129; `stale read refused` with D-129.
//@ also-verified: put
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
pub fn put(o: Option<&mut u32>) {
    if let Some(r) = o {
        *r = 5;
    }
}

pub fn host() {
    let mut c = 0u32;
    put(Some(&mut c));
    proof_assert!(c@ == 0);
}
