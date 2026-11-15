//@ expect: verify
//@ mechanism: a bool `SwitchInt` on a LITERAL condition skips the panic-arm obligation (its taken arm is meant to reach the enclosing gate as the literal-`false` returning-path fact), but a diverging THEN arm's fact is built as `!condition`, so `if true { panic!() }` produced `!true`, not `false`. That missed the literal route, became a returning-path fact premising every postcondition with `false`, and no lane charged the panic.
//@ mechanism: control for literal_true_switch_panic_arm_under_guard.rs: the same body, with the guard excluded by the precondition, so the unreachability obligation `!c` holds.
//@ accept-means: n/a (control)
//@ fixed-by: D-166 — `push_returning_path_fact` folds a negated literal before routing it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(!c)]
#[ensures(result == 1i32)]
pub fn f(c: bool) -> i32 {
    if c {
        let b = true;
        if b {
            panic!()
        }
    }
    1
}
