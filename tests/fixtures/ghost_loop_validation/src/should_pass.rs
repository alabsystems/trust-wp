// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_std::{ghost, prelude::*};

#[allow(dead_code)]
pub fn terminating_ghost_loop(x: u32) -> Ghost<u32> {
    ghost! {
        let mut i = x;
        while i > 0 {
            i -= 1;
        }
        i
    }
}

fn main() {}
