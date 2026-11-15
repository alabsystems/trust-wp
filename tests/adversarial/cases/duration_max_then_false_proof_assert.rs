//@ expect: reject
//@ mechanism: the false twin of duration_max_then_proof_assert_control, identical but for the
//@ mechanism: asserted constant. Checking the ground evaluator must not let a false assertion
//@ mechanism: through where the unchecked one panicked: a term with no `i64` value is no fact.
//@ accept-means: the proof_assert lane proves `d@ == 2 * 10^9` for `d = Duration::from_secs(1)`.
//@ fixed-by: D-137
//@ teeth: a driver panic on the unchecked evaluator (TEETH LOST: a crash is no verdict), FAILED
//@ teeth: with it checked; FAILED at the campaign base too, where `Duration::new`'s bound was not
//@ teeth: ground.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::time::Duration;

#[ensures(result)]
pub fn max_then_false_assert() -> bool {
    let max = Duration::new(u64::MAX, 999_999_999);
    let d = Duration::from_secs(1);
    proof_assert!(d@ == 2_000_000_000);
    max >= d
}
