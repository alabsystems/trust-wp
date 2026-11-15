//@ expect: verify
//@ mechanism: control for reassigned_borrow_new_target_write_lost — the same program asserting the TRUE half of its post-state: the borrow was reassigned away from `x` before the write, so `x` really is unchanged. It verifies, which is what makes its twin's accept a hole rather than over-refusal.
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
    let q: &mut i32 = &mut y;
    r = q;
    *r = 7;
    proof_assert!(x == 5i32);
}
