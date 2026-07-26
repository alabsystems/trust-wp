// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `#[trusted]` accepts module items.

use trust_wp_macros::{ensures, trusted};

#[trusted]
mod trusted_mod {
    use super::ensures;

    #[ensures(result == 1u32)]
    pub fn unchecked() -> u32 {
        1
    }
}

fn main() {
    let _ = trusted_mod::unchecked();
}
