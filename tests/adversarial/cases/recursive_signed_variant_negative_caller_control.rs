//@ expect: verify
//@ mechanism: a direct signed-machine variant uses its finite type minimum; negative values are valid, unlike mathematical Int variants.
// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n)]
pub fn countdown(n: i32) -> i32 {
    if n >= -1 { countdown(n - 1) } else { 0 }
}
