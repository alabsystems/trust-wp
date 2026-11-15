//@ expect: verify
//@ mechanism: control for logic_fn_body_some_call_renamed, differing in the claim alone: `result == None` is what `nothing(y)` returns, so the renamed call must be read as `nothing`.
//@ accept-means: n/a (control) — `caller(y)` is `nothing(y)`, which is `None`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn nothing(x: Int) -> Option<Int> {
    None
}

use crate::nothing as Some;

#[logic]
#[ensures(result == None)]
pub fn caller(y: Int) -> Option<Int> {
    Some(y)
}
