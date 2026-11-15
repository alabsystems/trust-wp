//@ expect: reject
//@ also-verified: g
//@ mechanism: the nested-tuple spelling of program_fn_pattern_param_contract_captures_caller_name. A
//@ mechanism: program function destructures its parameter two levels deep
//@ mechanism: (`((_c, a), _d): ((u32, u32), u32)`) and its `ensures` names the inner binding `a`. A
//@ mechanism: caller instantiates the callee's clause with the callee's PARAMETERS substituted, so a
//@ mechanism: binding left free is read in the caller's scope, where the caller's own `a` captures it.
//@ accept-means: the callee's postcondition was granted about the caller's `a` instead of the second
//@ accept-means: component of the argument's first component.
//@ WHY THE CONTRACT IS FALSE: `h(1)` is `g(((1, 7), 1))`, which returns 7, not 1. `g` itself is true
//@ WHY THE CONTRACT IS FALSE: and is credited on purpose.
//@ fixed-by: D-177 — the binding is the projection `__twp_arg0.0.1` in the one clause text the callee's own
//@ fixed-by: verification and every caller read.
//@ teeth: ACCEPTED (exit 0) with every crate checked out at the campaign base in place, and rejected
//@ teeth: (`h` FAILED) at the reviewed head; the isolating twin
//@ teeth: program_fn_nested_tuple_pattern_param_captures_caller_name_control.rs, which passes `a` in
//@ teeth: the slot the pattern reads, verifies on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn g(((_c, a), _d): ((u32, u32), u32)) -> u32 {
    a
}

#[ensures(result == a)]
pub fn h(a: u32) -> u32 {
    g(((a, 7), a))
}
