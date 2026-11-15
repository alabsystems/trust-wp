// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN twin of should_fail_fnptr_add: the fn-pointer call owes the
//! addition obligation, discharged by the precondition.

use trust_wp::{ensures, requires};

#[requires(x@ < 255)]
#[ensures(true)]
pub fn fnptr_ok(x: u8) -> u8 {
    let f: fn(u8, u8) -> u8 = <u8 as core::ops::Add>::add;
    f(x, 1)
}

fn main() {}
