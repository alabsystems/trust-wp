//@ expect: verify
//@ mechanism: a proof_assert after a call whose precondition is a ground term past `i64`. D-137 gave
//@ mechanism: `Duration::new` the carry bound `secs@ + nanos@ / 10^9 <= u64::MAX@`, which is ground
//@ mechanism: here, and an `Int` literal is an `i64`, so `u64::MAX` is the term
//@ mechanism: `4294967295 * 4294967296 + 4294967295`. The proof_assert lane's ground evaluator
//@ mechanism: (`ghost_flatten::eval_ground_int`) multiplied it unchecked: a debug build panicked
//@ mechanism: ("attempt to multiply with overflow") and the assertion was not proved; a release
//@ mechanism: build wraps it to -1. It is checked now, and a term with no `i64` value has no truth.
//@ accept-means: n/a (control) — `d@ == 10^9` for `d = Duration::from_secs(1)`, and `Duration::MAX`
//@ accept-means: is not shorter than one second.
//@ fixed-by: D-137
//@ teeth: `unknown (proof_assert not proved)` after the driver panic on the unchecked evaluator,
//@ teeth: verified with it checked (and at the campaign base, where `Duration::new`'s bound was not
//@ teeth: ground); its false twin is duration_max_then_false_proof_assert.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::Duration;

#[ensures(result)]
pub fn max_then_assert() -> bool {
    let max = Duration::new(u64::MAX, 999_999_999);
    let d = Duration::from_secs(1);
    proof_assert!(d@ == 1_000_000_000);
    max >= d
}
