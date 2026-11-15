//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_block_local_same_path with one block: a logic function declared in a block, alone under its path, calls `needs_pos` through the block's rename inside the precondition it requires. A fix that refuses a path two definitions share must still verify it.
//@ accept-means: n/a (control) — `k` calls `needs_pos` only where `y > 0`.
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
}
