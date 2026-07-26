// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct Ghost creation in program context should FAIL.

use trust_wp_std::ghost::Ghost;

#[allow(dead_code)]
pub fn explicit_create_ghost_in_program() {
    let _: Ghost<i32> = Ghost::new(1);
}

fn main() {}
