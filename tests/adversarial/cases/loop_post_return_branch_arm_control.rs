//@ expect: verify
//@ mechanism: control for loop_post_return_branch_arm: the same body, whose postcondition names the
//@ mechanism: value of each arm under its branch condition, is TRUE and proved from the arms merged
//@ mechanism: under the branch condition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(n > 5u32 ==> result == 1u32)]
#[ensures(n <= 5u32 ==> result == 2u32)]
pub fn g(n: u32) -> u32 {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    if n > 5 { 1 } else { 2 }
}
