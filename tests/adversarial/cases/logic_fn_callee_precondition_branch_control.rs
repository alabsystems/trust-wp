//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_else_branch, the arms swapped: the call is reached only where `y > 0`, so the precondition it owes under that arm's condition holds.
//@ accept-means: n/a (control) — the call sits in the arm whose condition is the callee's precondition.
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
pub fn caller(y: Int) -> Int {
    if y > 0 {
        needs_pos(y)
    } else {
        0
    }
}
