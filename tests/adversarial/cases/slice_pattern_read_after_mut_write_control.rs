//@ expect: verify
//@ mechanism: a slice pointer's length is part of the pointer value, so a switch on `PtrMetadata` of a borrow of `*a` demands only that `a`'s OWN storage is unchanged (`switch_discr_is_value_stable`, `Demand::SliceLength`), not its pointee. A slice pattern (`match &*a { [_x, _y] => .. }`) switches on exactly that length, so its arms are walked after a write through `a` where the switch used to owe the fail-closed `false`.
//@ mechanism: control: the two-element arm returns an element read back through the pattern's shared borrow of the written slice.
//@ xfail: a wrong reject, `f FAILED` on `(a@.len() == 2) ==> false`. The return sink reads a store through a `&mut` (`return_value_reads_stale_store`) and owes the fail-closed `false`; the arm's guard wraps it (`guard_branch_obligations_if`), and `fail_closed_marker_count` recognises only the bare literal, so the refutation is published instead of withheld. Before D-168 the switch itself owed a bare `false` and this was `unknown (refutation withheld)`.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a@.len() == 2)]
pub fn f(a: &mut [u32]) -> u32 {
    a[0] = 1;
    match &*a {
        [_x, y] => *y,
        _ => 0,
    }
}
