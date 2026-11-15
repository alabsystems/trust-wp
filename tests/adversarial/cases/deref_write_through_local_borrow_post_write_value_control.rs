//@ expect: verify
//@ xfail: `*b += 1` is recorded for the borrow chain as the raw `x + 1`, which the name lane reads
//@ xfail: at the post-write binding, so the premises state `x == 12 + 1` beside
//@ xfail: `x == (12 + 1) + 1` and the vacuity guard refuses the assertion. Recording the governed
//@ xfail: write's resolved value instead verifies this, and opens a path-local false accept where
//@ xfail: the owner is still a parameter's entry symbol on some path (D-171). Retire this directive
//@ xfail: when the post-write value is stated without reading the owner's name at the post-write
//@ xfail: binding on any path.
//@ xfail-verdict: unknown
//@ mechanism: control for deref_write_through_local_borrow_read_as_applied_twice: the same body
//@ mechanism: asserting the value the write leaves.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn once() {
    let mut x = 12i32;
    let b = &mut x;
    *b += 1;
    proof_assert!(x@ == 13);
}
