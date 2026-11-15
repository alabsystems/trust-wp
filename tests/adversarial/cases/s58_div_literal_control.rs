//@ expect: verify
//@ mechanism: control: a literal non-zero divisor owes a divisor obligation that is discharged
//@ mechanism: by the literal itself.
//@ WHY THE PROGRAM IS RIGHT: `% 7` and `/ 3` can neither divide by zero nor overflow (the
//@ WHY THE PROGRAM IS RIGHT: divisors are the constants 7 and 3, and neither is 0 or -1).
//@ teeth: verifies at campaign 03a35447 (wp-s58 probe r09, 2026-09-14).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(n: i32) -> i32 {
    let m = n % 7i32;
    m / 3i32
}
