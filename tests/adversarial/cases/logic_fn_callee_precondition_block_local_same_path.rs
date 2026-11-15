//@ expect: reject
//@ mechanism: two logic functions declared in two blocks of one function share a name, so rustc prints one path for both (`host::k`). What each body's calls denote was recorded per logic function BY PATH, so both bodies were read against one record: the first `k` calls `np(y)` under `use crate::needs_pos as np;`, the second under `use crate::free as np;`, and the first was read as calling `free`, which owes nothing. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition is credited `verified` because another logic function printed with the same path calls a function with no precondition under the same spelling.
//@ WHY IT IS FALSE: at `y == 0` the first `k` calls `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_` goal for it carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, on the rustc-resolution walk with its record keyed by path: `creusot_test::host::k verified ✓` twice. The same crate with both blocks renaming `needs_pos` is refuted twice on that build. The control is logic_fn_callee_precondition_block_local_same_path_control.rs.
//@ fixed-by: D-136
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
