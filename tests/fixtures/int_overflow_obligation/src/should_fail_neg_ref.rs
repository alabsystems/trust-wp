// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED: `-&i8` forwards to the checked negation; panics for `*x == i8::MIN`.

use trust_wp::ensures;

#[ensures(true)]
pub fn neg_ref(x: &i8) -> i8 {
    -x
}

fn main() {}
