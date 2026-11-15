//@ expect: verify
//@ xfail: the honest twin of s48v4_box_new_handback_vec_push is NOT provable today: with the Vec advanced at the `Box::new` call its post-state is unconstrained, so `v@.len() == n@ + 1` is REFUTED rather than merely unknown. Measured on this program: `proof_assert in creusot_test::k FAILED ✗` with a counterexample, base_exit_code=1. That is the price of the deletion in this shape, and it was not better before: with `Box::new` listed the build proved the FALSE twin instead. Retire this xfail when a write through a reborrow handed back out of a container flows back to the borrowed place.
//@ mechanism: control for the `Box::new` in-place handback arm — the same program asserting the length the push actually leaves.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn k() {
    let mut v: Vec<i32> = Vec::new();
    let n = v.len();
    let b = Box::new(&mut v);
    (**b).push(1);
    proof_assert!(v@.len() == n@ + 1);
}
