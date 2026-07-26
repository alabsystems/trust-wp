// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost erasure check: statement-form snapshot macros must allow `#[logic]`
//! calls inside their body without rejecting them as program-context logic
//! usage.
//!
//! Regression test for the syntax/12_ghost_code Creusot compat case (#9):
//! `snapshot! { logi_drop(x); };` lowers (under `cfg(trust_wp)`) to a block
//! whose tail is `Snapshot::<()>::new_phantom()`, not `Snapshot::capture(...)`,
//! so the validator's `snapshot_capture_depth` was not bumped while walking
//! the captured statements.  That caused the validator to reject the
//! `#[logic]` call as "called logic function in program context" and the
//! ghost API validator to misclassify the call as a ghost extraction.

#![allow(dead_code, unused_must_use)]

use trust_wp_std::{ghost::Snapshot, logic, snapshot};

#[logic]
fn logi_drop<T>(_: T) {}

/// Bare statement form: `snapshot! { stmt; }` with a discarded result.
pub fn snapshot_stmt_form() {
    let mut x = Vec::new();
    snapshot! { logi_drop(x); };
    x.push(0);
    assert!(x.len() == 1);
}

/// Statement form with an explicit binding to `_`.
pub fn snapshot_stmt_form_bound_to_discard() {
    let mut x = Vec::new();
    let _ = snapshot! { logi_drop(x); };
    x.push(0);
    assert!(x.len() == 1);
}

/// Expression form (non-unit body) — `Snapshot::capture(...)` is emitted
/// directly and already covered by the existing depth tracking; included
/// here to keep the two forms together for future maintenance.
pub fn snapshot_expr_form_capture() {
    let v: Vec<u32> = Vec::new();
    let _s: Snapshot<Vec<u32>> = snapshot! { v };
}

fn main() {}
