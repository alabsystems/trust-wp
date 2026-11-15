//@ expect: verify
//@ mechanism: control for logic_fn_body_view_call_renamed_in_macro_generated_fn, differing in the renaming `use` alone: the generated `view(y)` is the prelude's `view`, the view of an `Int`, which is `y`.
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

macro_rules! mk {
    ($name:ident) => {
        #[logic]
        #[ensures(result == y)]
        pub fn $name(y: Int) -> Int {
            view(y)
        }
    };
}

mk!(caller);
