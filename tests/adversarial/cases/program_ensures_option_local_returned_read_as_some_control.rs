//@ expect: verify
//@ mechanism: control for program_ensures_option_local_returned_read_as_some, differing in `#[requires(o != None)]` alone: every argument the function admits is `Some`, and it returns it through a local.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(o != None)]
#[ensures(result != None)]
pub fn prog(o: Option<u32>) -> Option<u32> {
    let p = o;
    p
}
