// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! proof_assert in a loop body reading a local the loop carries round its
//! back edge (D-187).
//!
//! The program-point walk follows each acyclic path from the entry once, so
//! it reached each assertion on the FIRST iteration and read `y` and `i` at
//! their first-iteration values (0), crediting both FALSE assertions: with
//! n = 2 the second iteration reads `y == 5` and `v == 1`.

use trust_wp::proof_assert;

fn written_later(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    while i < n {
        proof_assert!(y == 0i32);
        y = 5i32;
        i += 1;
    }
}

fn counter_copy(n: u32) {
    let mut i = 0u32;
    while i < n {
        let v = i;
        proof_assert!(v == 0u32);
        i += 1;
    }
}

fn main() {
    written_later(2);
    counter_copy(2);
}
