//@ expect: verify
//@ mechanism: control for moved_borrow_source_reassigned_write_lost — the same program asserting the post-state both writes actually leave behind.
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k() {
    let mut x = 5i32;
    let mut y = 5i32;
    let mut r: &mut i32 = &mut x;
    let r2 = r;
    r = &mut y;
    *r2 = 7;
    *r = 8;
    proof_assert!(x == 7i32 && y == 8i32);
}
