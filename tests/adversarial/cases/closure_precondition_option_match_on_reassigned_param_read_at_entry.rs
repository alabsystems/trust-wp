//@ expect: reject
//@ mechanism: the `Option`-match spelling of closure_precondition_names_uncaptured_variable_read_at_entry.rs.
//@ mechanism: A by-value `mut x: Option<u32>` pinned to `None` by `#[requires(x.is_none())]`, overwritten
//@ mechanism: with `Some(5)`, then a closure whose precondition is `match x { Some(_) => false, None => true }`
//@ mechanism: called directly. The caller's obligation for that precondition reads `x` at its entry value.
//@ mechanism: The match reads a constant the phantom upgrade split from the one `x.is_none()` constrains, so
//@ mechanism: the stale entry fact does not reach the arms. A link of the two reads, which D-218
//@ mechanism: refuses, let it discharge the obligation; D-218 withholds the split's model instead. The
//@ mechanism: `x.is_none()` spelling of the closure's precondition is credited with or without the link.
//@ accept-means: a closure call's precondition is discharged from a by-value parameter's entry value after
//@ accept-means: the body overwrote the parameter, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: at the call `x` is `Some(5)`, so the closure's precondition is false.
//@ fixed-by: the hole is OPEN in its other spelling, closure_precondition_names_uncaptured_variable_read_at_entry.rs;
//@ fixed-by: this spelling is rejected while the split is not linked (D-218).
//@ teeth: MEASURED ACCEPTED, exit 0, with the link: `caller verified`. `caller FAILED`
//@ teeth: without it and before D-218; `caller unknown (refutation withheld)` with D-218.
//@ also-verified: caller::{closure#2}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x.is_none())]
pub fn caller(mut x: Option<u32>) {
    x = Some(5);
    let c = #[requires(match x { Some(_) => false, None => true })]
    || {
        let _ = x;
    };
    c();
}
