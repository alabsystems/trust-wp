//@ expect: reject
//@ mechanism: the Creusot-dialect twin of v7_callsite_old_at_caller_entry: `result == *p` needs
//@ mechanism: no `old`, but the argument `x`, passed after a store `*x = 5` its translation does
//@ mechanism: not see, is read as the pointee's ENTRY value (`deref_store_staleness`); the
//@ mechanism: call's preconditions were already refused for it, and its postconditions were not.
//@ accept-means: a callee's clause about its argument's value at the call is a fact about the
//@ accept-means: caller's entry value.
//@ WHY THE CONTRACT IS FALSE: the result is 5, and the entry `*x` is arbitrary.
//@ fixed-by: D-101
//@ teeth: MEASURED on d73d0571 (debug driver): `get_caller_false verified`. On the D-101 tree:
//@ teeth: unknown.
//@ also-verified: get
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == *p)]
pub fn get(p: &mut i32) -> i32 {
    *p
}

#[ensures(result == *x)]
pub fn get_caller_false(x: &mut i32) -> i32 {
    *x = 5;
    get(x)
}
