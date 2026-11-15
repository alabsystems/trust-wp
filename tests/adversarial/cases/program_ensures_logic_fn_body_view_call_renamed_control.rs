//@ expect: verify
//@ mechanism: control for program_ensures_logic_fn_body_view_call_renamed, differing in the renaming `use` alone: `wrapper`'s `view(y)` is the builtin view, so `wrapper(x@) == x@` holds.
//@ accept-means: n/a (control) — `wrapper(x@)` is `x@`.
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

#[ensures(wrapper(x@) == x@)]
pub fn prog(x: u32) {}
