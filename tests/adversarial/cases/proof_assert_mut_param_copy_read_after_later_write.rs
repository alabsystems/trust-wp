//@ expect: reject
//@ mechanism: the copy spelling of proof_assert_mut_param_snapshot_read_after_later_write: `let a = *x`
//@ mechanism: reads a `&mut` parameter's pointee, a constant is written through the parameter, and
//@ mechanism: `proof_assert!(a == 5)` is read with `a == x_current` and `x_current == 5`, the pointee
//@ mechanism: named by one name before and after the write. The by-value parameter's spelling is
//@ mechanism: proof_assert_param_copy_reads_later_rebind; no snapshot and no precondition is involved.
//@ accept-means: a `proof_assert!` about a copy taken before a write is credited from the write.
//@ WHY THE CONTRACT IS FALSE: `copy_then_write(&mut 1)`: `a` is 1, so `a@ == 5` is false at the
//@ WHY THE CONTRACT IS FALSE: assertion.
//@ fixed-by: D-185 (the write's current-value binding `*x == 5` is no fact about the entry pointee
//@ fixed-by: the copy names; the assertion is unknown)
//@ teeth: LIVE: ACCEPTED, `proof_assert in creusot_test::copy_then_write verified` and the function
//@ teeth: `verified`, on the campaign driver, on it with the legacy deref-write handlers made to
//@ teeth: record the resolved value, and before and after D-101 (the same body in a probe crate).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
pub fn copy_then_write(x: &mut i32) {
    let a = *x;
    *x = 5;
    proof_assert!(a@ == 5);
}
