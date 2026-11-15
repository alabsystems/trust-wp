//@ expect: reject
//@ mechanism: every call binds `value` (and `default`, `arg`, `rhs`) to its first argument that is
//@ mechanism: not `self`, for std spec texts that spell a parameter so, whatever the callee's own
//@ mechanism: parameters are called. A local function's clause that reads a module constant named
//@ mechanism: `value` is proved over the constant and granted to each caller over the argument.
//@ accept-means: a callee's clause was proved with one meaning of a name and granted with another.
//@ WHY THE CONTRACT IS FALSE: `c` returns `f(1, 9)`, which is 5, not 9.
//@ fixed-by: D-179 — a clause that reads a name every call binds by position, with no parameter of
//@ fixed-by: that name, is refused at discovery.
//@ teeth: ACCEPTED (exit 0, `f verified` and `c verified`) on the merge of wp-campaign into wp-s117.
//@ teeth: clause_param_named_value_bound_at_call_control, whose `value` is a parameter, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub const value: u32 = 5;

#[ensures(result == value)]
pub fn f(x: u32, y: u32) -> u32 {
    5u32
}

#[ensures(result == 9u32)]
pub fn c() -> u32 {
    f(1u32, 9u32)
}
