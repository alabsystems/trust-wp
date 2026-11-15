//@ expect: reject
//@ verdict: failed
//@ fn-failed: k
//@ also-verified: h
//@ mechanism: The twin of call_result_result_switch_edge_then_match_control.rs whose second conjunct claims the
//@ mechanism: arm `h`'s contract excludes: `h(0)` is `Err`. The bridge relates the two reads, so this is
//@ mechanism: not a split D-218 withholds.
//@ accept-means: a premise scoped to a call-result edge proves the arm its callee excludes.
//@ fixed-by: n/a — rejected before D-218 and with it.
//@ teeth: `k FAILED` before D-218 and with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(match result { Ok(v) => v == x && x != 0, Err(_) => x == 0 })]
pub fn h(x: u32) -> Result<u32, ()> {
    if x == 0 { Err(()) } else { Ok(x) }
}

#[ensures(result)]
pub fn k() -> bool {
    h(1).is_ok() && h(0).is_ok()
}
