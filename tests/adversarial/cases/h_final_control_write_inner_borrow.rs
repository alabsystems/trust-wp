//@ expect: verify
//@ mechanism: control for the h_final_* family — a FINAL reborrow whose whole-borrow equality Creusot proves; a fix that makes every reborrow fresh breaks this
//@ xfail: D-185 refuses the assertion as a stale read: it reads the borrow `r` after `**x = value`
//@ xfail: writes through `x`, whose alias class `r` (a reborrow of `**x`) is in; the alias analysis
//@ xfail: does not follow the redirect `*x = b` that makes that store miss `r`. A TRUE assertion,
//@ xfail: not credited and not refuted (measured: verified on 67fd4ea7).
//@ xfail-verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn write_inner_borrow<'a, T>(x: &mut &'a mut T, b: &'a mut T, value: T) {
    let r = &mut **x;
    let snap = snapshot!(&mut **x);
    *x = b;
    **x = value; // r does not refer to the same borrow, so r is in fact final !
    proof_assert!(r == *snap);
}
