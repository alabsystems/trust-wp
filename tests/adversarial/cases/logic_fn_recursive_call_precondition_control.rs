//@ expect: verify
//@ mechanism: control for logic_fn_recursive_call_precondition, the recursion guard raised by one: `x > 2` keeps `x - 2` inside `f`'s own precondition, and the precondition the call owes is `x - 2 > 0`, which `x > 2` gives.
//@ accept-means: n/a (control) — every recursive call is inside the precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
#[ensures(true)]
#[variant(x)]
pub fn f(x: Int) -> Int {
    if x > 2 {
        f(x - 2)
    } else {
        0
    }
}
