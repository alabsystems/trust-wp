//@ expect: verify
//@ mechanism: control for the unnested `&mut &mut` prophecy gap — the TRUE reading of the same program; the counterexample reports `inner_current = 1` beside `r_current = 0` and `v = 0`, i.e. the write through the unnested borrow reaches neither link of the chain.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn mirror2_true() {
    let mut v: i32 = 0;
    let mut r = &mut v;
    let x = &mut r;
    let inner: &mut i32 = &mut **x;
    *inner = 1;
    // TRUE: `*inner = 1` writes through the chain x -> r -> v.
    proof_assert!(v == 1);
}
