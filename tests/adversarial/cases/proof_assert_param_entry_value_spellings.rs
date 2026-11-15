//@ expect: reject
//@ mechanism: two more spellings of the by-value parameter whose entry and current value the
//@ mechanism: proof_assert lane read by one name (D-241): a copy of a GENERIC parameter taken before a
//@ mechanism: re-bind follows the re-bind (`let c = x; x = y; proof_assert!(c == x)`), as
//@ mechanism: proof_assert_param_copy_reads_later_rebind.rs does for `u32`; and a `snapshot!` of a
//@ mechanism: parameter follows a later write, as snapshot_follows_later_write_unseen.rs does for a
//@ mechanism: local. (A tuple parameter's field store is the struct case's spelling, recorded in
//@ mechanism: proof_assert_after_param_field_write_keeps_entry_requires.rs.)
//@ accept-means: an assertion about a by-value parameter after a write is credited from the value the
//@ accept-means: parameter had at entry, or a copy of it from the value written after the copy.
//@ WHY THE CONTRACT IS FALSE: `generic_copy_then_rebind(0, 1)` asserts `0 == 1`;
//@ WHY THE CONTRACT IS FALSE: `snapshot_of_entry_claims_current(0)` asserts `0 == 5`.
//@ fixed-by: D-241: the entry value of a re-bound by-value parameter has a symbol of its own in every
//@ fixed-by: value the walks recorded and in its `#[requires]`; the snapshot freezes the binding it reads.
//@ teeth: MEASURED on D-240: `generic_copy_then_rebind` ACCEPTED, `snapshot_of_entry_claims_current`'s
//@ teeth: assertion `verified`; with D-241 each is FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
pub fn generic_copy_then_rebind<T: Copy + PartialEq>(mut x: T, y: T) {
    let c = x;
    x = y;
    proof_assert!(c == x);
}

#[requires(x@ == 0)]
pub fn snapshot_of_entry_claims_current(mut x: u32) {
    let s = snapshot!(x);
    x = 5;
    proof_assert!((*s)@ == 5);
}
