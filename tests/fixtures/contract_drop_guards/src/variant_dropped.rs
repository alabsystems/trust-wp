// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp::{check, variant};

#[check(terminates)]
#[variant('a')]
fn malformed_variant(n: i32) -> i32 {
    if n <= 0 { 0 } else { malformed_variant(n - 1) }
}

fn main() {
    let _ = malformed_variant(3);
}
