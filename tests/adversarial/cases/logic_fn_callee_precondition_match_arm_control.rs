//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_match_arm: the arm tests the binder before the call, so the precondition owed under the pattern and the test holds.
//@ accept-means: n/a (control) — the call is reached only where its argument is positive.
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
pub fn caller(o: Option<Int>) -> Int {
    match o {
        Some(v) => if v > 0 { needs_pos(v) } else { 0 },
        None => 0,
    }
}
