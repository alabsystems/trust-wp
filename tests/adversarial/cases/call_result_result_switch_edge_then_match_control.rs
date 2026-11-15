//@ expect: verify
//@ mechanism: The `Result` spelling of call_result_option_switch_edge_then_match_control.rs: the edge
//@ mechanism: `$call.is_ok()` reads the call's result at the opaque `Result` sort, the postcondition's match
//@ mechanism: at `ResultIntInt` through a bridge that does not carry `is_ok`.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — verified before D-218 and with it; see call_result_option_switch_edge_then_match_control.rs.
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
    h(1).is_ok() && h(0).is_err()
}
