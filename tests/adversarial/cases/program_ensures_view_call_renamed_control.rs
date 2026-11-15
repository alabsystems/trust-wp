//@ expect: verify
//@ mechanism: control for program_ensures_view_call_renamed, differing in the renaming `use` alone: `view(x@)` is the prelude's `view`, so the clause holds.
//@ accept-means: n/a (control) — the view of an `Int` is itself.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn succ(x: Int) -> Int {
    x + 1
}

#[ensures(view(x@) == x@)]
pub fn prog(x: u32) {}
