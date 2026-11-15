//@ expect: verify
//@ mechanism: control for program_ensures_view_call_renamed_chained_comparison, differing in the renaming `use` alone: `view(x)` is the prelude's `view`, `5`, and `0 <= 5 < 6` holds.
//@ accept-means: n/a (control) — the chained comparison holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn seven(x: u32) -> Int {
    7
}

#[requires(x@ == 5)]
#[ensures(0 <= view(x) < 6)]
pub fn prog(x: u32) -> u32 {
    x
}
