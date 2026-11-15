//@ expect: reject
//@ mechanism: a snapshot of a `&mut` parameter's pointee, then a constant written through the
//@ mechanism: parameter, then `proof_assert!` of the snapshot against the written constant. The
//@ mechanism: proof_assert lane names the pointee by one name, `x_current`, at every program point:
//@ mechanism: the snapshot binds `s == x_current` and the write binds `x_current == 5`, so the
//@ mechanism: snapshot reads a value written after it was taken. The same single name reads
//@ mechanism: `*x += 1` as `x_current == x_current + 1`, which is why the CLI fixture's
//@ mechanism: `double_increment` is reported vacuous (proof_assert_mut_param_double_increment_control).
//@ mechanism: No precondition is involved, so withdrawing the pointee's entry facts
//@ mechanism: (proof_assert_mut_param_pointee_store_reads_entry_requires) does not reach it; the scalar
//@ mechanism: local's spelling is snapshot_follows_later_write_unseen.
//@ accept-means: a `proof_assert!` is credited from a write that happened after the value it names
//@ accept-means: was read.
//@ WHY THE CONTRACT IS FALSE: `snap_then_write(&mut 1)`: the snapshot holds 1, so `*s == 5` is false
//@ WHY THE CONTRACT IS FALSE: at the assertion.
//@ fixed-by: D-185 (the write's current-value binding `*x == 5` is no fact about the entry pointee
//@ fixed-by: the copy names; the assertion is unknown)
//@ teeth: LIVE: ACCEPTED, `proof_assert in creusot_test::snap_then_write verified` and the function
//@ teeth: `verified`, on the campaign driver, on it with the legacy deref-write handlers made to
//@ teeth: record the resolved value, and before and after D-101's one elaboration (the same body in
//@ teeth: a probe crate), so it predates D-101, which turned the double increment vacuous.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
pub fn snap_then_write(x: &mut i32) {
    let s: Snapshot<i32> = snapshot!(*x);
    *x = 5;
    proof_assert!((*s)@ == 5);
}
