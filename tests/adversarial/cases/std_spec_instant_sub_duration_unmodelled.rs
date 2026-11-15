//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: `Instant - Duration` panics ("overflow when subtracting duration from instant") on a
//@ mechanism: bound the platform clock sets, and `<Instant as Sub>::sub` names it and the saturating
//@ mechanism: `Instant - Instant` alike, so the one spec the path finds said the result saturates to
//@ mechanism: 0. The call site now tells the two apart. Under D-121 the requirement was a refused
//@ mechanism: marker wherever `Rhs` is not `Self`; under D-137 it is `checked_sub`'s own bound,
//@ mechanism: `self@ >= rhs@`, which `u64::MAX` seconds does not meet.
//@ accept-means: `Instant - Duration` is trusted not to panic again.
//@ fixed-by: D-121, then D-137 — the operator owes the `Some` bound of `checked_sub`.
//@ WHY THE CONTRACT IS FALSE: subtracting `u64::MAX` seconds from any instant leaves the clock's
//@ WHY THE CONTRACT IS FALSE: range, so the only call `f` makes panics.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, with the std spec tables reverted to the
//@ teeth: base; `unknown` on D-121's marker; FAILED under D-137. Its twin
//@ teeth: std_spec_instant_sub_instant_control subtracts an `Instant` instead.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::time::{Duration, Instant};

#[ensures(true)]
pub fn f() -> bool {
    let t = Instant::now() - Duration::from_secs(u64::MAX);
    t == t
}
