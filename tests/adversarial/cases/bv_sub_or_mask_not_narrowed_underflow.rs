//@ expect: reject
//@ verdict: failed
//@ fn-failed: or_step
//@ mechanism: D-115's narrowing admits right shifts and AND masks only, the two operations that
//@ mechanism: cannot raise a non-negative value. An OR can: `x | 1` is `x + 1` at every even `x`, so
//@ mechanism: `x - (x | 1)` underflows there. A rule that admitted every bitwise operator on the
//@ mechanism: same operand bounds the difference below by 0 and proves the u8 overflow check, the
//@ mechanism: function's only obligation.
//@ accept-means: `or_step(0)` computes `0 - (0 | 1) = 0 - 1` in u8 and panics; an accept claims it
//@ accept-means: returns.
//@ fixed-by: n/a (shape gate for D-115)
//@ teeth: ACCEPTED on a local build whose `narrowed_from` answered true for every shape; FAILED with
//@ teeth: the rule as D-115 states it and with the rule switched off.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn or_step(x: u8) -> u8 {
    x - (x | 1)
}
