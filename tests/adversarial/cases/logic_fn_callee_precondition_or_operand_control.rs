//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_or_operand, the left operand negated: the call is evaluated only where `y <= 0` fails, which is the callee's precondition.
//@ accept-means: n/a (control) — the call is reached only at `y > 0`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> bool {
    y <= 0 || needs_pos(y) > 0
}
