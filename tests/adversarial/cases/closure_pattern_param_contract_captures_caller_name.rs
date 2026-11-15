//@ expect: reject
//@ also-verified: h::{closure#2}
//@ mechanism: the closure spelling of program_fn_pattern_param_contract_captures_caller_name. A
//@ mechanism: closure destructures its parameter (`|(p, _q): (u32, u32)|`) and its `ensures` names
//@ mechanism: the binding `p`. The enclosing function calls it; the closure's postcondition is
//@ mechanism: instantiated with the closure's PARAMETERS substituted, so a binding left free is read
//@ mechanism: in the caller's scope, where the caller's own parameter `p` captures it.
//@ accept-means: the closure's postcondition was granted about the caller's `p` instead of the first
//@ accept-means: component of the argument.
//@ WHY THE CONTRACT IS FALSE: `h(1)` returns `f((7, 1))`, which is 7, not 1. The closure's own
//@ WHY THE CONTRACT IS FALSE: contract is true and is credited on purpose.
//@ fixed-by: D-177 — a closure's clause text names the binding as its parameter's projection
//@ fixed-by: (`p` is `__twp_arg0.0`), as a function's does.
//@ teeth: ACCEPTED (exit 0) with the driver crate checked out at the campaign base in place, and
//@ teeth: rejected (`h` FAILED) at the reviewed head; the isolating twin
//@ teeth: closure_pattern_param_contract_captures_caller_name_control.rs, which passes `(1, 7)`,
//@ teeth: verifies on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(p@ == 1)]
#[ensures(result@ == 1)]
pub fn h(p: u32) -> u32 {
    let f = #[ensures(result == p)] |(p, _q): (u32, u32)| p;
    f((7, 1))
}
