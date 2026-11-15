//@ expect: verify
//@ mechanism: the control of assertion_reads_field_or_snapshot_before_untranslated_write.rs: the same field
//@ mechanism: writes and snapshot with a right-hand side the translator reads (the parameter `x`), and each
//@ mechanism: assertion claims the place holds it, which is proved only from the value the write stores.
//@ accept-means: n/a (control) — each place holds `x` at the assertion in every execution.
//@ fixed-by: n/a (control)
//@ teeth: every assertion verified on the campaign tip and with D-217.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unused_assignments)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub a: u32,
    pub b: u32,
}

pub fn tuple_field(x: u32) {
    let mut t = (0u32, 1u32);
    t.0 = x;
    proof_assert!(t.0 == x);
}

pub fn struct_field(x: u32) {
    let mut s = S { a: 0, b: 1 };
    s.b = x;
    proof_assert!(s.b == x);
}

pub fn snapshot_of_local(x: u32) {
    let mut a = 1u32;
    a = x;
    let s = snapshot!(a);
    proof_assert!(*s == x);
}
