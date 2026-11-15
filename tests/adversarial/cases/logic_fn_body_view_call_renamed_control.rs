//@ expect: verify
//@ mechanism: control for logic_fn_body_view_call_renamed, differing in the renaming `use` alone: `view(y)` is the prelude's `view`, the view of an `Int`, which is `y`, so a fix that refuses a renamed `view` must still verify this.
//@ accept-means: n/a (control) — `view(y)` is the builtin view and `result == y` holds.
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
#[ensures(result == y)]
pub fn caller(y: Int) -> Int {
    view(y)
}
