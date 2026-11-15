//@ expect: verify
//@ mechanism: control that keeps this family from being credited to a blanket refusal of nested `&mut &mut`: the SAME chain written through `**x` directly, with no unnesting reborrow, propagates correctly today — only the unnested `&mut **x` spelling loses the prophecy equations, so this must keep verifying while its twins are fixed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn mirror5_true() {
    let mut v: i32 = 0;
    let mut r = &mut v;
    let x = &mut r;
    **x = 1;
    proof_assert!(v == 1);
}
