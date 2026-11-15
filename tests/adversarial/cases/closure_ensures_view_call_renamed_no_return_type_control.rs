//@ expect: verify
//@ mechanism: control for closure_ensures_view_call_renamed_no_return_type, differing in the renaming `use` alone: `view(result)` is the prelude's `view` of the closure's result, which is its argument `5`.
//@ accept-means: n/a (control) — the closure returns its argument, whose view the `requires` fixes at `5`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn seven(x: u32) -> Int {
    7
}

pub fn prog() -> u32 {
    let c = #[requires(x@ == 5)]
    #[ensures(view(result) == 5)]
    |x: u32| x;
    c(5)
}
