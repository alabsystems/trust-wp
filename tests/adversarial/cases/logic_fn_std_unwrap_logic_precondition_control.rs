//@ expect: verify
//@ mechanism: control for logic_fn_std_unwrap_logic_precondition, differing in the caller's `#[requires]` alone: the option it admits is `Some`, which is what `unwrap_logic` requires.
//@ accept-means: n/a (control) — the call is inside `unwrap_logic`'s precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(o != None)]
#[ensures(true)]
pub fn caller(o: Option<Int>) -> Int {
    o.unwrap_logic()
}
