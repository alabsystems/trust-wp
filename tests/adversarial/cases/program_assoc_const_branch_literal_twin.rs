//@ expect: verify
//@ mechanism: the literal twin of program_assoc_const_branch_control: the same guard with
//@ mechanism: `i32::MAX` written as its value. It verifies, which is what says the xfail there is
//@ mechanism: the associated constant's translation and not the guard or the addition.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (control; `bump verified` on the campaign head)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ >= 0)]
#[ensures(result@ > 0)]
pub fn bump(x: i32) -> i32 {
    if x < 2147483647 {
        x + 1
    } else {
        x
    }
}
