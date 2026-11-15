// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED (stale value): the parameter `x` is reassigned before an annotated
//! loop; the in-loop `x + k` must use the reassigned value (x + 200), not the
//! entry value bounded by the precondition.

use trust_wp::{ensures, invariant, requires};

#[requires(x@ <= 50)]
#[ensures(true)]
#[invariant(k@ <= 10)]
pub fn shifted(mut x: u8) -> u8 {
    x = x + 200;
    let mut k: u8 = 0;
    let mut acc: u8 = 0;
    while k < 10 {
        acc = x + k;
        k += 1;
    }
    acc
}

fn main() {}
