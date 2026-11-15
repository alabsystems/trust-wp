//@ expect: verify
//@ mechanism: control for closure_requires_view_call_renamed_unannotated_param, differing in the renaming `use` alone: `view(x)` is the prelude's `view`, so `c(5u32)` meets the closure's precondition.
//@ accept-means: n/a (control) — the call is inside the closure's precondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn seven(x: u32) -> Int {
    7
}

#[ensures(true)]
pub fn prog() -> u32 {
    let c = #[requires(view(x) == 5)]
    |x| x;
    c(5u32)
}
