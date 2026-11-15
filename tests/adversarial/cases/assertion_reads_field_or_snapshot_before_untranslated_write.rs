//@ expect: reject
//@ mechanism: two more routes into the `proof_assert!` walk's stale read of
//@ mechanism: assertion_reads_local_before_untranslated_reassignment.rs. A write into a tuple or struct field
//@ mechanism: whose value the translator leaves untranslated (`t.0 = x | u32::MAX`, an associated constant
//@ mechanism: used directly as an operand; `t.1 = q as usize`, a pointer-to-integer cast) is skipped by
//@ mechanism: `on_assign_projected`, so the field keeps its earlier value; and a snapshot taken after an
//@ mechanism: untranslated assignment to a local reads the local's earlier value. A fix of the local route
//@ mechanism: alone leaves both open. The control
//@ mechanism: assertion_reads_field_or_snapshot_after_translated_write_control.rs translates the same writes.
//@ accept-means: `tuple_field(0)`, `struct_field(0)` and `snapshot_of_local(0)` reach their assertion with
//@ accept-means: `u32::MAX` in the place, and `ptr_cast_field(q)` with the address of `q`; an accept claims
//@ accept-means: each assertion that the place is still `0` holds.
//@ fixed-by: OPEN — committed RED rather than hidden; closes with
//@ fixed-by: assertion_reads_local_before_untranslated_reassignment.rs when the walk binds an untranslated
//@ fixed-by: write, whole or projected, to a symbol of its site and a snapshot reads that binding.
//@ teeth: every assertion verified, exit 0, on the campaign tip and with D-217.
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
    let mut t = (0u32, 0u32);
    t.0 = x | u32::MAX;
    proof_assert!(t.0 == 0u32);
}

pub fn struct_field(x: u32) {
    let mut s = S { a: 0, b: 0 };
    s.b = x | u32::MAX;
    proof_assert!(s.b == 0u32);
}

pub fn ptr_cast_field(q: *const u8) {
    let mut t = (0usize, 0usize);
    t.1 = q as usize;
    proof_assert!(t.1 == 0usize);
}

pub fn snapshot_of_local(x: u32) {
    let mut a = 0u32;
    a = x | u32::MAX;
    let s = snapshot!(a);
    proof_assert!(*s == 0u32);
}
