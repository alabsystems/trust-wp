//@ expect: reject
//@ mechanism: a bool `SwitchInt` on a LITERAL condition skips the panic-arm obligation (its taken arm is meant to reach the enclosing gate as the literal-`false` returning-path fact), but a diverging THEN arm's fact is built as `!condition`, so `if true { panic!() }` produced `!true`, not `false`. That missed the literal route, became a returning-path fact premising every postcondition with `false`, and no lane charged the panic.
//@ mechanism: the literal comes from a `const` item and the arm is `unreachable!()`.
//@ accept-means: an `unreachable!()` that every execution reaches is credited as unreachable.
//@ WHY THE CONTRACT IS FALSE: `ON` is `true`, so `f()` always reaches `unreachable!()` and panics.
//@ teeth: MEASURED ACCEPTED at the campaign tip before the fix, exit 0: `f verified ✓`.
//@ verdict: error
//@ refused-with: vacuous (contradictory premises)
//@ fixed-by: D-166 — `push_returning_path_fact` folds a negated literal before routing it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

const ON: bool = true;

#[ensures(true)]
pub fn f() {
    if ON {
        unreachable!()
    }
}
