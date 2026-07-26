// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(proc_macro_hygiene)]

use trust_wp::{ensures, invariant};

#[ensures(result >= 0)]
fn malformed_per_loop_invariant(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    #[invariant('a')]
    while i < n {
        sum += i;
        i += 1;
    }
    sum
}

fn main() {
    let _ = malformed_per_loop_invariant(5);
}
