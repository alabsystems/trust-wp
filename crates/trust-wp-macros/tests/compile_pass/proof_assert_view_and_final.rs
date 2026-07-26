// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unexpected_cfgs)]

use trust_wp_macros::proof_assert;

fn proof_assert_tuple_field_view() {
    let _pair = (6i32, 42i32);
    proof_assert!(_pair.0@ == 6 && _pair.1@ == 42);
}

fn proof_assert_method_call_with_implication() {
    proof_assert!(true ==> true);
}

fn main() {}
