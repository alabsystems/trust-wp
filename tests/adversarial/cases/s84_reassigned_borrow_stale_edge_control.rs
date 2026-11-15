//@ expect: verify
//@ mechanism: control for s84_reassigned_borrow_stale_edge — `x` is untouched by a write through the reassigned borrow, and the lane must still prove that.
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k(p: &mut i32) {
    let mut x = 5i32;
    let mut r = &mut x;
    r = p;
    *r = 7;
    proof_assert!(x == 5i32);
}
