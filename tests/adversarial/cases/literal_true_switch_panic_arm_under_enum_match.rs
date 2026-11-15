//@ expect: reject
//@ mechanism: a bool `SwitchInt` on a LITERAL condition skips the panic-arm obligation (its taken arm is meant to reach the enclosing gate as the literal-`false` returning-path fact), but a diverging THEN arm's fact is built as `!condition`, so `if true { panic!() }` produced `!true`, not `false`. That missed the literal route, became a returning-path fact premising every postcondition with `false`, and no lane charged the panic.
//@ mechanism: nested under an enum `match` arm, whose lane guards in-arm facts with the variant test.
//@ accept-means: a panic reached whenever `o` is `Some` is credited as unreachable.
//@ WHY THE CONTRACT IS FALSE: `f(Some(0))` panics.
//@ teeth: MEASURED ACCEPTED at the campaign tip before the fix, exit 0: `f verified ✓`. The isolating control is literal_true_switch_panic_arm_under_enum_match_control.rs.
//@ verdict: failed
//@ fn-failed: f
//@ fixed-by: D-166 — `push_returning_path_fact` folds a negated literal before routing it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(o: Option<u32>) {
    match o {
        Some(_) => {
            let b = true;
            if b {
                panic!()
            }
        }
        None => {}
    }
}
