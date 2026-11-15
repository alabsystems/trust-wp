//@ expect: verify
//@ mechanism: the control of assertion_reads_local_before_untranslated_reassignment.rs: the same assignments,
//@ mechanism: and the assertion compares the local with a copy taken after it, which holds whatever value
//@ mechanism: the walk gives the untranslated assignment. A fix that refuses the assertion instead of binding
//@ mechanism: the assignment loses this control.
//@ accept-means: n/a (control) — a local equals its own copy.
//@ fixed-by: n/a (control)
//@ teeth: verified on the campaign tip and with D-217.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unused_assignments)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn ptr_cast(q: *const u8) {
    let mut a = 0usize;
    a = q as usize;
    let b = a;
    proof_assert!(a == b);
}

pub fn assoc_const(x: f64) {
    let mut m = 0u32;
    m = (x + f64::EPSILON) as u32;
    let k = m;
    proof_assert!(m == k);
}
