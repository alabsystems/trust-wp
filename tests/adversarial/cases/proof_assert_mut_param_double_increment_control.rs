//@ expect: verify
//@ xfail: the proof_assert lane names a `&mut` parameter's pointee by one name at every program
//@ xfail: point, so `*x += 1` is read as `x_current == x_current + 1`: both assertions are
//@ xfail: reported `unknown (vacuous proof: base assertions are UNSAT ...)` and the function is
//@ xfail: `unknown` on a fail-closed `false`. The CLI fixture simple_examples::double_increment is
//@ xfail: this program without the bound, and making the legacy deref-write handlers record the
//@ xfail: resolved value leaves that fixture vacuous.
//@ xfail-verdict: unknown
//@ mechanism: control for proof_assert_mut_param_snapshot_read_after_later_write: two increments
//@ mechanism: through a `&mut` parameter with a snapshot before each, and assertions relating the
//@ mechanism: snapshots and the current value. The bound keeps both additions in range.
//@ accept-means: n/a (control)
//@ teeth: n/a (price control; the same body's assertions verified before D-101's one elaboration
//@ teeth: and are vacuous since)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*x)@ < 2147483646)]
#[ensures((^x)@ == (*x)@ + 2)]
pub fn double_increment(x: &mut i32) {
    let start: Snapshot<i32> = snapshot!(*x);
    *x += 1;
    let mid: Snapshot<i32> = snapshot!(*x);
    *x += 1;
    proof_assert!((*mid)@ == (*start)@ + 1);
    proof_assert!((*x)@ == (*mid)@ + 1);
}
