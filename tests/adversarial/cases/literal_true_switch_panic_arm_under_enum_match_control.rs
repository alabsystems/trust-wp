//@ expect: verify
//@ xfail: the unreachability obligation `!(o is Some)` is proved UNSAT under `requires(o == None)`, but strict certification declines the proof (`unknown (proof-trusted)`); before the fix this control "verified" only because the arm owed nothing.
//@ mechanism: a bool `SwitchInt` on a LITERAL condition skips the panic-arm obligation (its taken arm is meant to reach the enclosing gate as the literal-`false` returning-path fact), but a diverging THEN arm's fact is built as `!condition`, so `if true { panic!() }` produced `!true`, not `false`. That missed the literal route, became a returning-path fact premising every postcondition with `false`, and no lane charged the panic.
//@ mechanism: control for literal_true_switch_panic_arm_under_enum_match.rs: the same body with `Some` excluded by the precondition.
//@ accept-means: n/a (control)
//@ fixed-by: D-166 — `push_returning_path_fact` folds a negated literal before routing it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(o == None)]
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
