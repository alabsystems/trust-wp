// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test that old() is rejected in pearlite! (only valid in ensures)

use trust_wp_macros::pearlite;

fn main() {
    // old() is not valid in pearlite - only in ensures
    let _ = pearlite!(old(x) > 0);
}
