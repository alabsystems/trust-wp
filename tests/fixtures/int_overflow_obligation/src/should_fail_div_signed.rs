// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: signed `a / b` with `b != 0` but not excluding `MIN / -1`.
//! Creusot: `Int8.div` precondition `not (a = min_int /\ b = -1)`.

use trust_wp::{ensures, requires};

#[requires(b@ != 0)]
#[ensures(true)]
pub fn quot(a: i8, b: i8) -> i8 {
    a / b
}

fn main() {}
