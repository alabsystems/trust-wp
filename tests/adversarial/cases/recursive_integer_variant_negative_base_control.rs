//@ expect: verify
//@ mechanism: mathematical variants constrain the caller, so the final call from n=0 into the negative base case n=-1 is valid.
// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n@)]
pub fn countdown(n: i32) -> i32 {
    if n >= 0 { countdown(n - 1) } else { 0 }
}
