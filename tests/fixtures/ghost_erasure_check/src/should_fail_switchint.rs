// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost erasure check: `SwitchInt` leak case that should FAIL.
//!
//! This fixture exercises the primary MIR-only erasure check: runtime control
//! flow must not branch on a value derived from `Ghost<T>`.

use trust_wp_std::{ghost, ghost::Ghost};

/// Non-ghost control flow must not depend on a ghost-derived boolean.
///
/// Expected validation error:
/// ```text
/// error: runtime control flow depends on ghost-derived local
/// ```
#[allow(dead_code)]
pub fn branch_on_ghost_value() -> i32 {
    let ghost_flag: Ghost<bool> = ghost! { true };
    if *ghost_flag {
        1
    } else {
        2
    }
}

fn main() {}
