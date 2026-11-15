//@ expect: verify
//@ mechanism: a bool `SwitchInt` on a LITERAL condition skips the panic-arm obligation (its taken arm is meant to reach the enclosing gate as the literal-`false` returning-path fact), but a diverging THEN arm's fact is built as `!condition`, so `if true { panic!() }` produced `!true`, not `false`. That missed the literal route, became a returning-path fact premising every postcondition with `false`, and no lane charged the panic.
//@ mechanism: control: a literal `false` condition makes the panic arm dead, so no obligation is owed and nothing is refuted.
//@ accept-means: n/a (control)
//@ fixed-by: D-166 — `push_returning_path_fact` folds a negated literal before routing it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 1i32)]
pub fn f(c: bool) -> i32 {
    if c {
        let b = false;
        if b {
            panic!()
        }
    }
    let d = false;
    if d {
        unreachable!()
    }
    1
}
