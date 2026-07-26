// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(dead_code, unexpected_cfgs)]

#[trust_wp::logic]
fn logic_helper(x: i32) -> bool {
    x > 0
}

pub fn calls_logic_from_program(x: i32) -> bool {
    logic_helper(x)
}

fn main() {}
