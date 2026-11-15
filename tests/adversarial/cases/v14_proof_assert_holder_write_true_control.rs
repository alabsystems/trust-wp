//@ expect: verify
//@ xfail: D-129's price: a `proof_assert!` reading a local after a write through a holder of its
//@ xfail: borrow is refused whatever it claims, because the lane does not carry the write to the
//@ xfail: local; these TRUE assertions about the written value are refused with the false ones.
//@ xfail: Retire it when the lane applies a holder's write to the borrowed local; the reject case
//@ xfail: v14_proof_assert_reads_a_place_written_through_a_holder must still reject then.
//@ mechanism: the TRUE claims on v14_proof_assert_reads_a_place_written_through_a_holder's bodies:
//@ mechanism: after `*t.0 = 5` through a holder of `&mut c`, `c == 5`. It pins the direction a fix
//@ mechanism: must take: apply the write, not read the stale value.
//@ fixed-by: n/a (priced incompleteness)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn local_field_store_true() {
    let mut b = 0i32;
    let mut c = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = &mut c;
    *t.0 = 5i32;
    proof_assert!(c == 5i32);
}

pub fn param_aggregate_true(x: &mut i32) {
    let t = (&mut *x, 0i32);
    *t.0 = 5i32;
    proof_assert!(*x == 5i32);
}
