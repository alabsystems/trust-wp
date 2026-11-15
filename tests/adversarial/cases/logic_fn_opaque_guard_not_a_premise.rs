//@ expect: reject
//@ mechanism: an opaque `#[variant]` logic fn over a machine-integer parameter has the requires list `[written.., false guard, parameter ranges]`; a strip that removed the opaque guard only when it was LAST kept `false` as a premise of the function's own body goals, which then proved anything but for the vacuity check. The guard is now found after the written clauses (`logic_fn_verify::callee_preconditions::own_premises`).
//@ accept-means: a logic function's own body goals were proved from its opaque guard.
//@ WHY IT IS FALSE: at `n == 0` the body evaluates `needs_pos(0)`; the control differs in that literal alone.
//@ teeth: MEASURED on the commit before D-119: nothing examined (a function with no `ensures` got no lane; `0 verified`, exit 2). With the lane and the guard kept as a premise: `f unknown (logic callee precondition not proved)` from the vacuity check instead of the refutation.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::f
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

#[logic(opaque)]
#[requires(n >= 0)]
#[variant(n)]
pub fn f(n: Int, k: u8) -> Int {
    if n > 0 { f(n - 1, k) } else { needs_pos(0) }
}
