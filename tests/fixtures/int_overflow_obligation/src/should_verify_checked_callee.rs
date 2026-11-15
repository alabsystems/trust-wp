// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN twin of should_fail_vec_remove: a contract-free body calling a
//! callee whose checked spec precondition is discharged, and a total core
//! integer method.

use trust_wp::{ensures, requires};

#[requires(z@ != 0)]
#[ensures(result@ == 1)]
fn one(z: u8) -> u8 {
    z / z
}

pub fn checked_callee(x: u8) -> u8 {
    let _ = one(1);
    x.wrapping_add(1) / 2
}

fn main() {}
