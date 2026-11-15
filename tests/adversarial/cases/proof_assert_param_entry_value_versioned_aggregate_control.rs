//@ expect: verify
//@ mechanism: control for the by-value parameter entry/current versioning (D-241) on aggregates: a
//@ mechanism: struct, tuple or enum parameter written through a field or re-bound whole keeps its
//@ mechanism: `#[requires]` about its entry value, which the unwritten fields and copies taken before
//@ mechanism: the write read, while the written field reads the value stored. The walk rebinds the
//@ mechanism: parameter to the functional update of its value (`P(7, get_1(p))`); its own name was the
//@ mechanism: identity reset (#1500), which read the field just written at its entry value.
//@ accept-means: n/a (control) — every claim here holds in every execution.
//@ fixed-by: n/a (control)
//@ teeth: on D-240 `other_field`'s `p.a@ == 7`, `field_then_whole` and `tuple_field` are FAILED and
//@ teeth: `enum_rebind` `unknown`; all verified with D-241.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: u32,
    pub b: u32,
}

#[requires(p.a@ < 10)]
pub fn field_inc(mut p: P) {
    p.a = p.a + 1;
    proof_assert!(p.a@ < 11);
    let _ = p;
}

#[requires(p.b@ == 3)]
pub fn other_field(mut p: P) {
    p.a = 7;
    proof_assert!(p.b@ == 3);
    proof_assert!(p.a@ == 7);
    let _ = p;
}

#[requires(p.a@ == 3)]
pub fn copy_field_then_write(mut p: P) {
    let k = p.a;
    p.a = 7;
    proof_assert!(k@ == 3);
    let _ = p;
}

#[requires(p.a@ == 3 && p.b@ == 4)]
pub fn field_then_whole(mut p: P) {
    let k = p.a;
    p.a = 7;
    let m = p.a;
    p = P { a: 1, b: p.b };
    proof_assert!(k@ == 3 && m@ == 7 && p.a@ == 1 && p.b@ == 4);
}

#[requires(t.0@ == 1)]
pub fn tuple_field(mut t: (u32, u32)) {
    t.1 = 9;
    proof_assert!(t.0@ == 1 && t.1@ == 9);
    let _ = t;
}

#[requires(o == Some(3u32))]
pub fn enum_rebind(mut o: Option<u32>) {
    let k = o;
    o = None;
    proof_assert!(k == Some(3u32));
    proof_assert!(o == None);
}
