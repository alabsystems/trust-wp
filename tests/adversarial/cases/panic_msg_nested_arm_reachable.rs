//@ expect: reject
//@ verdict: failed
//@ fn-failed: diverging
//@ mechanism: the nested spelling of panic_msg_arm_reachable: the `panic!("msg")` arm sits under
//@ mechanism: an outer branch, so its prologue marker is `a ==> (b ==> false)` and the arm's goal
//@ mechanism: `a ==> !b`. They pair under the same outer guard and the marker is not counted
//@ mechanism: (D-141).
//@ accept-means: a nested reachable panic is credited, or its refutation withheld as `unknown`.
//@ WHY THE CONTRACT IS FALSE: `diverging(true, true)` panics.
//@ teeth: MEASURED on one build with local knobs: with the pairing disabled, or read only at the
//@ teeth: top level, this nesting keeps its marker counted and `diverging` is withheld as
//@ teeth: `unknown`; here it is `FAILED`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn diverging(a: bool, b: bool) -> i32 {
    if a {
        if b {
            panic!("both");
        } else {
            1
        }
    } else {
        2
    }
}
