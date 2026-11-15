// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! RED twin of should_verify_index_contractless: the guard admits `i == 4`,
//! one past the end. A contract-free body owes its index bounds goal (D-95).

pub fn index_unguarded(a: [u8; 4], i: usize) -> usize {
    if i <= 4 {
        let _ = a[i];
        i + 1
    } else {
        0
    }
}

fn main() {}
