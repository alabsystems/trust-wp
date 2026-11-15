//@ expect: reject
//@ verdict: unknown
//@ refused-with: k unknown (refutation withheld: a phantom sort upgrade split `$call_4`
//@ also-verified: h
//@ mechanism: The twin of call_result_option_switch_edge_then_match_control.rs whose second conjunct claims the
//@ mechanism: arm `h`'s contract excludes: `h(0)` is `None`. The second call's premise is scoped to the edge
//@ mechanism: `$call.is_some()`, which reads the constant the first call's match abandoned, so the
//@ mechanism: refutation is withheld (D-218).
//@ accept-means: a premise scoped to a call-result edge proves the arm its callee excludes.
//@ fixed-by: n/a — rejected before D-218 and with it.
//@ teeth: `k FAILED` before D-218; `k unknown (refutation withheld)` with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(match result { Some(v) => v == x && x != 0, None => x == 0 })]
pub fn h(x: u32) -> Option<u32> {
    if x == 0 { None } else { Some(x) }
}

#[ensures(result)]
pub fn k() -> bool {
    h(1).is_some() && h(0).is_some()
}
