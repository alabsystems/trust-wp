//@ expect: reject
//@ mechanism: a law's postcondition is exposed unproved in non-strict mode, so its ensures lane does not run, but its body goals are still owed: the call in its body owes the callee's precondition (`logic_fn_verify::callee_preconditions`).
//@ accept-means: a law's body calls are never owed.
//@ WHY IT IS FALSE: at `x == 0` the law's body evaluates `needs_pos(0)`.
//@ teeth: MEASURED on the commit before D-119: nothing examined (`law postcondition unverified`, `0 verified`, exit 2); the call is owed whether or not the law's postcondition is proved.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::l
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

#[logic(law)]
#[ensures(true)]
pub fn l(x: Int) {
    let _ = needs_pos(x);
}
