//@ expect: verify
//@ mechanism: the TRUE claim on proof_assert_after_param_field_write_keeps_entry_requires.rs's body. It pins the direction a fix must take: model the write, not refuse the assertion.
//@ accept-means: n/a (control) — the assertion is TRUE; an XPASS means the lane sees the write.
//@ fixed-by: D-241: the proof_assert lane binds a by-value parameter written through a field to the functional update of its value, so the TRUE post-write value verifies; xfail retired.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub a: u32,
    pub b: u32,
}

#[requires(p.a@ == 3)]
pub fn k(mut p: P) {
    p.a = 7;
    proof_assert!(p.a@ == 7);
}
