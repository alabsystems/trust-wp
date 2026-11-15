//@ expect: verify
//@ mechanism: The user-callee spelling of duration_checked_add_max_boundary_control.rs: D-169 scopes the
//@ mechanism: second call's postcondition to the edge `$call.is_some()` of the first, read at the opaque
//@ mechanism: `Option` sort, while the first call's postcondition matches the same `$call` at `OptionInt`
//@ mechanism: under a fresh symbol. This body's goal does not depend on the two being one, so it verifies;
//@ mechanism: D-218 withholds refutations only.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — verified before D-218 and with it; it keeps call_result_option_switch_edge_then_match_claimed_some.rs honest.
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
    h(1).is_some() && h(0).is_none()
}
