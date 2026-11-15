//@ expect: verify
//@ xfail: the honest twin of s48v4_box_new_handback_deref is NOT provable today, and that is the residual incompleteness this front did not close: advancing `x` at the `Box::new` call havocs it, so `x` after the write is unconstrained and the TRUE value is unrecoverable. Measured on this control program: `status=unknown reason=sort-coercion bridge in negated goal`, base_exit_code=2. Retire this xfail when a write through a reborrow handed back out of a container flows back to the borrowed place.
//@ mechanism: control for the `Box::new` handback arm — the same program asserting the value the write actually leaves behind.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn k() {
    let mut x = 5i32;
    let b = Box::new(&mut x);
    let r: &mut i32 = *b;
    *r = 7;
    proof_assert!(x == 7i32);
}
