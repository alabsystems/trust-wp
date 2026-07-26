// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct Ghost extraction in program context should FAIL.

use trust_wp_std::{ghost, ghost::Ghost};

#[allow(dead_code)]
pub fn explicit_into_inner_ghost_in_program() {
    let g: Ghost<i32> = ghost! { 2 };
    let _: i32 = Ghost::into_inner(g);
}

fn main() {}
