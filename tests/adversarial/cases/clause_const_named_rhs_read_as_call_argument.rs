//@ expect: reject
//@ mechanism: the `rhs` spelling of clause_const_named_value_read_as_call_argument, over a
//@ mechanism: one-parameter callee: every call binds `rhs` to its only argument.
//@ accept-means: a callee's clause was proved with one meaning of a name and granted with another.
//@ WHY THE CONTRACT IS FALSE: `c` returns `f(9)`, which is 5, not 9.
//@ fixed-by: D-179 — a clause that reads a name every call binds by position, with no parameter of
//@ fixed-by: that name, is refused at discovery.
//@ teeth: ACCEPTED (exit 0, `f verified` and `c verified`) on the merge of wp-campaign into wp-s117.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub const rhs: u32 = 5;

#[ensures(result == rhs)]
pub fn f(x: u32) -> u32 {
    5u32
}

#[ensures(result == 9u32)]
pub fn c() -> u32 {
    f(9u32)
}
