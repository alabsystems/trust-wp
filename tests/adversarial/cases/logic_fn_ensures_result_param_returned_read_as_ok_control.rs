//@ expect: verify
//@ mechanism: control for logic_fn_ensures_result_param_returned_read_as_ok, differing in a `#[requires]` that the parameter is `Ok` alone.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(match r { Ok(_) => true, Err(_) => false })]
#[ensures(match result { Ok(_) => true, Err(_) => false })]
pub fn caller(r: Result<Int, Int>) -> Result<Int, Int> {
    r
}
