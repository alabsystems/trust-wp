// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost context call-purity check that should FAIL.

use trust_wp_std::prelude::*;

#[check(terminates)]
fn terminating() {}

#[allow(dead_code)]
pub fn calls_terminating_from_ghost() {
    ghost! {
        terminating();
    };
}

fn main() {}
