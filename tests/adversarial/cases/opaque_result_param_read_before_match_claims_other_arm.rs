//@ expect: reject
//@ verdict: unknown
//@ refused-with: p unknown (sort-coercion bridge in negated goal
//@ mechanism: The twin of opaque_result_param_read_before_match_control.rs whose clause claims the arm the
//@ mechanism: precondition excludes; the bridge's demotion withholds it as it does the control.
//@ accept-means: a precondition read before a `Result` match proves the arm it excludes.
//@ fixed-by: n/a — rejected before D-218 and with it.
//@ teeth: `unknown` over the bridge before D-218 and with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(r.is_ok())]
#[ensures(match r { Ok(_) => false, Err(_) => true })]
pub fn p(r: Result<u32, u32>) {}
