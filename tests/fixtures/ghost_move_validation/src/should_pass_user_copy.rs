// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression fixture for #1981: user-defined Copy types must not be
//! rejected inside ghost blocks.

use trust_wp_std::ghost;

#[derive(Copy, Clone)]
struct Point {
    x: i32,
    y: i32,
}

pub fn copy_user_defined_copy_in_ghost(point: Point) {
    let _ = ghost! {{
        let _a = point;
        let _b = point;
    }};
}

fn main() {}
