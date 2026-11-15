//@ expect: verify
//@ mechanism: control for own_assertion_refuted_function_lane.rs: the same function with a TRUE assertion keeps its function-level credit once its own assertion is proved
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
#[ensures(result@ == x@ + 1)]
pub fn add_one(x: u32) -> u32 {
    let y = x + 1;
    proof_assert!(y@ == x@ + 1);
    y
}
