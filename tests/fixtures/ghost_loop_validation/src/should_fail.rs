// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_std::{ghost, ghost::Ghost};

#[allow(dead_code)]
pub fn non_terminating_ghost_loop() -> Ghost<i32> {
    ghost! {
        loop {}
    }
}

fn main() {}
