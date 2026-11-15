// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! proof_assert in a loop placed BEFORE the loop's own test (D-188).
//!
//! The in-body pass stated the loop condition at every assertion in the loop
//! body, so each FALSE assertion here was proved from the test it precedes:
//! with n = 0 each runs once with i = 0 before the test ends the loop.

use trust_wp::proof_assert;

fn before_break_test(n: u32) {
    let mut i = 0u32;
    loop {
        proof_assert!(i < n);
        if i >= n {
            break;
        }
        i += 1;
    }
}

fn in_while_condition_block(n: u32) {
    let mut i = 0u32;
    while {
        proof_assert!(i < n);
        i < n
    } {
        i += 1;
    }
}

fn main() {
    before_break_test(0);
    in_while_condition_block(0);
}
