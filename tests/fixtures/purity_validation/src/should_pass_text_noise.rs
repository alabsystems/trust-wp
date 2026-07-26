// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(dead_code, unexpected_cfgs)]

use trust_wp::logic::Int;

#[trust_wp::logic]
fn int_param_with_non_int_match(x: Int, y: i32) -> Int {
    // dead / % proof_assert!(false) Secret { value: 1 } bag[0]
    let _noise = "match x { 0 => x, _ => x } dead / % proof_assert!(false)";
    let _raw = r##"hidden_default(x) Secret { value: 1 } bag[0]"##;
    match y {
        0 => x,
        _ => Int(1),
    }
}

fn main() {}
