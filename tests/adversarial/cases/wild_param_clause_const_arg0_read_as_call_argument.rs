//@ expect: reject
//@ mechanism: a `_` parameter has no source name. The clause's `arg0` is the module constant in `f`'s
//@ mechanism: own lane, and every call binds `arg0` to the first argument (a std spec's positional
//@ mechanism: alias), so a caller of `f(9)` was granted `result == 9`.
//@ accept-means: a callee's clause was proved with one meaning of a name and granted with another.
//@ WHY THE CONTRACT IS FALSE: `c` returns `f(9)`, which is 5, not 9.
//@ fixed-by: D-179 — a clause that reads a name every call binds by position, with no parameter of
//@ fixed-by: that name, is refused at discovery (the `_` parameter's own name is `__twp_arg0`).
//@ teeth: ACCEPTED (exit 0, `f verified` and `c verified`) on the merge of wp-campaign into wp-s117.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub const arg0: u32 = 5;

#[ensures(result == arg0)]
pub fn f(_: u32) -> u32 {
    5u32
}

#[ensures(result == 9u32)]
pub fn c() -> u32 {
    f(9u32)
}
