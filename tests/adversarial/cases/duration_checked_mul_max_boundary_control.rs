//@ expect: verify
//@ xfail: a wrong reject, `f unknown (refutation withheld)`. D-169 scopes the second conjunct's premises
//@ xfail: to the edge `$call.is_some()` of the first; the encoder meets that call's result first as a
//@ xfail: receiver of `is_some()` (an uninterpreted `Option`) and later as a `match` scrutinee, where it
//@ xfail: upgrades the variable to the `OptionInt` datatype with a fresh symbol (`PhantomVariableUpgrade`),
//@ xfail: so the edge and the `checked_mul` postcondition speak of two unrelated constants and the model
//@ xfail: that refutes `result` describes no execution. D-218 withholds that refutation; it does not link
//@ xfail: the two reads, since a link lets a stale earlier read prove an arm.
//@ xfail-verdict: unknown
//@ mechanism: `Duration::checked_mul` is `None` exactly when the product is past `Duration::MAX`: its
//@ mechanism: seconds are `secs * rhs` plus the carry out of `nanos * rhs`, Creusot's contract.
//@ mechanism: `(6148914691236517205 s + 333_333_333 ns) * 3` is exactly `Duration::MAX`, `Some`;
//@ mechanism: `2^63 s * 2` is `Duration::MAX` and one nanosecond, `None`.
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
    Duration::new(6_148_914_691_236_517_205, 333_333_333).checked_mul(3).is_some()
        && Duration::from_secs(9_223_372_036_854_775_808).checked_mul(2).is_none()
}
