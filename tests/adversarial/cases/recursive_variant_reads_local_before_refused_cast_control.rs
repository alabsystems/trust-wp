//@ expect: verify
//@ mechanism: the control of recursive_variant_reads_local_before_refused_cast.rs: the same bodies with `m`
//@ mechanism: first bound to `n` and then reassigned `0`, which the recursive call-site extraction
//@ mechanism: translates, so the variant check reads the value the program passes (`0 < n`), not the
//@ mechanism: earlier binding (`n < n`, false).
//@ accept-means: n/a (control) — each function calls itself with `0` and terminates.
//@ fixed-by: n/a (control)
//@ teeth: verified (`termination`, each function) when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(f16)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n@)]
pub fn spin_f16(n: u32, h: f16) {
    if n == 0 {
        return;
    }
    let mut m = n;
    m = 0u32;
    spin_f16(m, h);
}

#[check(terminates)]
#[variant(n@)]
pub fn spin_assoc_const(n: u32, x: f64) {
    if n == 0 {
        return;
    }
    let mut m = n;
    m = 0u32;
    spin_assoc_const(m, x);
}

#[check(terminates)]
#[variant(n@)]
pub fn spin_const_item(n: u32, x: f64) {
    if n == 0 {
        return;
    }
    let mut m = n;
    m = 0u32;
    spin_const_item(m, x);
}
