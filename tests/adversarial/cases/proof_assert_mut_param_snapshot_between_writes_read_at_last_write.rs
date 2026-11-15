//@ expect: reject
//@ mechanism: two constant writes through a `&mut` parameter with a snapshot between them, then
//@ mechanism: `proof_assert!` of the snapshot against the second constant. With the pointee named by
//@ mechanism: one name at every program point the snapshot reads the last write.
//@ accept-means: a `proof_assert!` about a snapshot is credited from a write made after it was taken.
//@ WHY THE CONTRACT IS FALSE: `snap_between_writes(&mut 1)`: the snapshot holds 5, so `*m == 7` is
//@ WHY THE CONTRACT IS FALSE: false at the assertion.
//@ fixed-by: not a fix: since D-101's one elaboration both writes are read at the one name, the
//@ fixed-by: premises contradict each other and the vacuity check refuses the assertion.
//@ teeth: ACCEPTED (the assertion and the function `verified`) before D-101, the same body in a
//@ teeth: probe crate; rejected as vacuous since. The guard for a fix of
//@ teeth: proof_assert_mut_param_snapshot_read_after_later_write that names the pointee per write
//@ teeth: but reads a snapshot at the wrong one.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*x)@ == 1)]
pub fn snap_between_writes(x: &mut i32) {
    *x = 5;
    let m: Snapshot<i32> = snapshot!(*x);
    *x = 7;
    proof_assert!((*m)@ == 7);
}
