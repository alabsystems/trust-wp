//@ expect: verify
//@ mechanism: control for logic_fn_body_view_call_local_fn, differing in the local function's name alone (`bump`): `view(y)` is then the prelude's `view`, which is `y`.
//@ accept-means: n/a (control) — `view(y)` is the builtin view and `result == y` holds.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod m {
    use creusot_std::prelude::*;

    #[logic]
    pub fn bump(x: Int) -> Int {
        x + 1
    }

    #[logic]
    #[ensures(result == y)]
    pub fn caller(y: Int) -> Int {
        view(y)
    }
}
