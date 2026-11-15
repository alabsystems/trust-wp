//@ expect: verify
//@ xfail: a wrong reject, `f unknown (refutation withheld)`. D-169 scopes the second conjunct's premises
//@ xfail: to the edge `$call.is_some()` of the first; the encoder meets that call's result first as a
//@ xfail: receiver of `is_some()` (an uninterpreted `Option`) and later as a `match` scrutinee, where it
//@ xfail: upgrades the variable to the `OptionInt` datatype with a fresh symbol (`PhantomVariableUpgrade`),
//@ xfail: so the edge and the `checked_add` postcondition speak of two unrelated constants and the model
//@ xfail: that refutes `result` describes no execution. D-218 withholds that refutation; it does not link
//@ xfail: the two reads, since a link lets a stale earlier read prove an arm.
//@ xfail-verdict: unknown
//@ mechanism: `Duration::checked_add` is `None` exactly past `Duration::MAX` (`u64::MAX` seconds and
//@ mechanism: 999_999_999 nanoseconds), Creusot's contract. The sum that lands on `MAX` is `Some`;
//@ mechanism: one nanosecond more is `None`. Its twins claim each side of the boundary wrongly.
//@ accept-means: n/a (control) — this contract is TRUE (`f()` returns true under stock rustc).
//@ fixed-by: n/a (control)
//@ teeth: control — FAILED under the pre-D-138 spec (`None => true` states neither side), verified under it.
//@ teeth: `f FAILED` on `result` under D-169 without D-218, `unknown (refutation withheld)` with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::Duration;

#[ensures(result)]
pub fn f() -> bool {
    Duration::from_secs(u64::MAX).checked_add(Duration::new(0, 999_999_999)).is_some()
        && Duration::new(u64::MAX, 999_999_999).checked_add(Duration::from_nanos(1)).is_none()
}
