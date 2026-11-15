//@ expect: reject
//@ also-verified: g
//@ mechanism: the `requires` spelling of program_fn_pattern_param_contract_captures_caller_name. A
//@ mechanism: program function destructures its parameter (`(a, _b): (u32, u32)`) and its
//@ mechanism: precondition names the binding `a`. A caller owes the callee's `requires` with the
//@ mechanism: callee's PARAMETERS substituted; a binding left free is read in the caller's scope,
//@ mechanism: where the caller's own parameter `a` captures it, so `h` discharged `a > 0` about
//@ mechanism: its own `a` while it passes 0 as the first component.
//@ accept-means: a caller discharged a callee's precondition about its own variable instead of the
//@ accept-means: argument it passes: a division by zero is reached with the crate clean.
//@ WHY THE CONTRACT IS FALSE: `h(1)` calls `g((0, 1))`, whose precondition `0 > 0` fails, and
//@ WHY THE CONTRACT IS FALSE: `g` divides 100 by 0. `g` itself is true and is credited on purpose.
//@ fixed-by: D-177 — the callee's clause text names the binding as its parameter's projection
//@ fixed-by: (`a` is `__twp_arg0.0`), the one text its own verification and every caller read.
//@ teeth: ACCEPTED (exit 0) with the driver crate checked out at the campaign base in place, and
//@ teeth: rejected (`h` FAILED) at the reviewed head; the isolating twin
//@ teeth: program_fn_pattern_param_requires_captures_caller_name_control.rs, which passes `(a, 0)`,
//@ teeth: verifies on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a > 0u32)]
pub fn g((a, _b): (u32, u32)) -> u32 { 100 / a }

#[requires(a > 0u32)]
pub fn h(a: u32) -> u32 { g((0, a)) }
