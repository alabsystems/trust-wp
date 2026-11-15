//@ expect: verify
//@ mechanism: control for logic_fn_body_view_call_renamed_through_uncontracted_callee, differing in the renaming `use` alone: `wrapper`'s `view(y)` is the builtin view, `y`, and `caller` unfolds that definition.
//@ accept-means: n/a (control) — `wrapper(y)` is `y` and `result == y` holds.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn succ(x: Int) -> Int {
    x + 1
}

#[logic]
pub fn wrapper(y: Int) -> Int {
    view(y)
}

#[logic]
#[ensures(result == y)]
pub fn caller(y: Int) -> Int {
    wrapper(y)
}
