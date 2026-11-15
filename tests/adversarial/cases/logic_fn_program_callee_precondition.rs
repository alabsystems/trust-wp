//@ expect: reject
//@ mechanism: a logic body calls a program function; Creusot admits no program call in logic, and the encoder reads it as an uninterpreted placeholder, so no lane owed the callee's `requires` and the ensures lane credited the function. A call rustc resolves to a local function the logic lane does not read, a program function among them, is refused (D-136).
//@ accept-means: a logic function that calls a program function outside its precondition is credited `verified`.
//@ WHY IT IS FALSE: at `y == 0` the body calls `prog(0)`, and `prog` requires `x@ > 0`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `creusot_test::caller verified ✓` beside `prog verified ✓`, the call read as an uninterpreted placeholder.
//@ fixed-by: D-119
//@ verdict: unknown
//@ refused-with: which the logic lane does not read
//@ also-verified: prog
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ > 0)]
#[ensures(result == x)]
pub fn prog(x: i32) -> i32 {
    x
}

#[logic]
#[ensures(true)]
pub fn caller(y: i32) -> i32 {
    prog(y)
}
