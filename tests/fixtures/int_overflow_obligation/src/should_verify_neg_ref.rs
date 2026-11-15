// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! GREEN twin of `should_fail_neg_ref`: the negation is guarded.

use trust_wp::{ensures, requires};

#[requires(x@ > -128)]
#[ensures(true)]
pub fn neg_ref_ok(x: &i8) -> i8 {
    -x
}

fn main() {}
