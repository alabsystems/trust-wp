//@ expect: verify
//@ mechanism: control for program_ensures_boxed_option_deref_returned_read_as_some, differing in `#[requires(*b != None)]` alone: every argument the function admits is `Some`, and it returns it.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(*b != None)]
#[ensures(result != None)]
pub fn prog(b: Box<Option<u32>>) -> Option<u32> {
    *b
}
