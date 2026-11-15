//@ expect: verify
//@ mechanism: control for logic_fn_branch_assertion_refuted, differing in the literal alone: the assertion holds wherever its arm is taken, and not in the other arm, so a goal that dropped the branch condition would refute it.
//@ accept-means: n/a (control) — the assertion holds under its arm's condition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result >= 0)]
pub fn f(x: Int) -> Int {
    if x > 0 {
        proof_assert!(x >= 1);
        x
    } else {
        0
    }
}
