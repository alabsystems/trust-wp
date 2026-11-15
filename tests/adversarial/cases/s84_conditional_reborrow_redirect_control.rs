//@ expect: verify
//@ xfail: the exact post-state of s84_conditional_reborrow_redirect is NOT provable today — the write through the redirected borrow is dropped at the join. Measured on 684821d0: FAILED, base_exit_code=1. Retire this xfail when a write through a borrow whose target differs per branch is merged as a conditional write to each target.
//@ mechanism: control for s84_conditional_reborrow_redirect — the exact conditional post-state of both targets.
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub fn k(c: bool) {
    let mut x = 5i32;
    let mut y = 5i32;
    let mut t: &mut i32 = &mut x;
    if c {
        t = &mut y;
    }
    *t = 7;
    proof_assert!((c && x == 5i32 && y == 7i32) || (!c && x == 7i32 && y == 5i32));
}
