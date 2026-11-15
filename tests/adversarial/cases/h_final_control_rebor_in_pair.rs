//@ expect: verify
//@ mechanism: control for the h_final_* family — a FINAL reborrow whose whole-borrow equality Creusot proves; a fix that makes every reborrow fresh breaks this
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[allow(unused)]
pub fn rebor_in_pair() {
    let mut x = 12;
    let mut y = 13;
    let mut p = (&mut x, 12);
    let s = snapshot!(p.0);
    let b = &mut *p.0;
    proof_assert!(*s == b);
    p.0 = &mut y;
}
