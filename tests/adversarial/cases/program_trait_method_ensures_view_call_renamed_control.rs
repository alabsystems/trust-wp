//@ expect: verify
//@ mechanism: control for program_trait_method_ensures_view_call_renamed, differing in the renaming `use` alone: `view(result@)` is the prelude's `view`, so both clauses hold.
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

pub trait T {
    #[ensures(view(result@) == result@)]
    fn get(&self) -> u32;
}

pub struct S;

impl T for S {
    #[ensures(view(result@) == result@)]
    fn get(&self) -> u32 {
        0
    }
}
