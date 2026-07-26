// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp::proof_assert;

pub fn diverging_branch_before_assert(flag: bool) {
    let y = if flag {
        1i32
    } else {
        panic!("flag was false");
    };
    proof_assert!(y == 1i32);
}

fn main() {
    diverging_branch_before_assert(true);
}
