// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

use trust_wp_macros::proof_assert;

fn proof_assert_non_rust_quantifier_form_compiles() {
    proof_assert!(forall<i> i == i);
    proof_assert!(forall<x: i32> x >= 0 ==> x >= 0);
    proof_assert!(exists<y: i32> y == y);
}

fn main() {}
