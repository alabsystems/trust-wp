//@ expect: reject
//@ mechanism: a bool `SwitchInt` on a LITERAL condition skips the panic-arm obligation (its taken arm is meant to reach the enclosing gate as the literal-`false` returning-path fact), but a diverging THEN arm's fact is built as `!condition`, so `if true { panic!() }` produced `!true`, not `false`. That missed the literal route, became a returning-path fact premising every postcondition with `false`, and no lane charged the panic.
//@ mechanism: nested under a guard, the fact became `c ==> !true`: no obligation, and a postcondition premise instead.
//@ accept-means: a panic reached whenever `c` holds is credited as unreachable with no precondition excluding `c`.
//@ WHY THE CONTRACT IS FALSE: `f(true)` panics.
//@ teeth: MEASURED ACCEPTED at the campaign tip before the fix, exit 0: `f verified ✓`. The isolating control is literal_true_switch_panic_arm_guard_false_control.rs (the same body under `requires(!c)`), which verifies.
//@ verdict: failed
//@ fn-failed: f
//@ fixed-by: D-166 — `push_returning_path_fact` folds a negated literal before routing it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(c: bool) {
    if c {
        let b = true;
        if b {
            panic!()
        }
    }
}
