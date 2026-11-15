//@ expect: verify
//@ mechanism: control for program_ensures_view_call_renamed_impl_trait_return, differing in the renaming `use` alone: `view(x)` is the prelude's `view`, which the `requires` fixes at `5`.
//@ accept-means: n/a (control) — the view of `x` is `5` wherever `prog` may be called.
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
#[ensures(view(x) == 5)]
pub fn prog(x: u32) -> impl Sized {
    x
}
