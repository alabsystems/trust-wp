// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp::{ensures, requires};

#[requires('a')]
#[ensures(result == 0)]
fn malformed_requires(_x: i32) -> i32 {
    0
}

fn main() {
    let _ = malformed_requires(1);
}
