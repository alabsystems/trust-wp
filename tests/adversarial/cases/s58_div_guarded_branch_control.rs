//@ expect: verify
//@ mechanism: control: a divisor guarded by an `if d != 0` branch must still verify — the
//@ mechanism: branch's path condition is available at the division's program point.
//@ WHY THE PROGRAM IS RIGHT: the division runs only under `d != 0 && d != -1`.
//@ teeth: verifies at campaign 03a35447 (wp-s58 probe r08, 2026-09-14).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(d: i32) -> i32 {
    if d != 0 && d != -1 {
        10i32 / d
    } else {
        0i32
    }
}
