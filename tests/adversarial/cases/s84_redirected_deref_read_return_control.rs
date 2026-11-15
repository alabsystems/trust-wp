//@ expect: verify
//@ xfail: the honest twin of s84_redirected_deref_read_return — `result == 5` was refuted before the return gate (the lane read `*t` as `x`) and is refused by it now. Measured on both the pre-gate and the post-gate build: FAILED, exit 1 in each. Retire this xfail when the return lane follows a pointer-slot redirect.
//@ mechanism: control for s84_redirected_deref_read_return — the same program with the true postcondition.
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
#[ensures(result == 5i32)]
pub fn k() -> i32 {
    let mut x = 0i32;
    let mut y = 5i32;
    let mut t: &mut i32 = &mut x;
    let tt: &mut &mut i32 = &mut t;
    *tt = &mut y;
    *t
}
