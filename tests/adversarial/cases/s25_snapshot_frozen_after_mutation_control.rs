//@ expect: verify
//@ mechanism: snapshot frozen at capture — control (true relation to the frozen value)
//@ fixed-by: 3820919 (s25 vacuous whole-value equality)
//@ accept-means: n/a (control) — rejected before 3820919 for the same root cause
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn snapshot_true() {
    let mut v: Vec<i32> = Vec::new();
    let old = snapshot!(v);
    v.push(1i32);
    proof_assert!(v@ == old@.push_back(1i32));
}
