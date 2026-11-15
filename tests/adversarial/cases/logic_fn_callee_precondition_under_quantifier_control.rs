//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_under_quantifier, the call guarded by an implication inside the binder: `i > 0 ==> needs_pos(i) == i` evaluates the call only where its precondition holds.
//@ accept-means: n/a (control) — the implication's premise is the callee's precondition.
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
pub fn caller() -> bool {
    pearlite! { forall<i: Int> i > 0 ==> needs_pos(i) == i }
}
