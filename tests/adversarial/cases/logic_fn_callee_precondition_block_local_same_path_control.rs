//@ expect: verify
//@ xfail: the price of D-136: two local functions print as `host::k`, so which body's type-checked form a record found by that path is cannot be told, and both bodies, which make calls, are refused. One such function alone verifies (logic_fn_callee_precondition_block_local_single_control.rs).
//@ mechanism: control for logic_fn_callee_precondition_block_local_same_path, differing in the first `k`'s `#[requires]` alone: every argument it admits is inside `needs_pos`'s precondition, so both functions' claims are true.
//@ accept-means: n/a (control) — the first `k` calls `needs_pos` only where `y > 0`, and the second calls `free`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
pub fn free(x: Int) -> Int {
    x
}

pub fn host() {
    {
        use crate::needs_pos as np;
        #[logic]
        #[requires(y > 0)]
        #[ensures(true)]
        fn k(y: Int) -> Int {
            np(y)
        }
    }
    {
        use crate::free as np;
        #[logic]
        #[ensures(true)]
        fn k(y: Int) -> Int {
            np(y)
        }
    }
}
