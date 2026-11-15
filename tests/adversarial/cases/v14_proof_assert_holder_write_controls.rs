//@ expect: verify
//@ mechanism: controls for v14_proof_assert_reads_a_place_written_through_a_holder: a holder that
//@ mechanism: holds ANOTHER local's borrow, written through, leaves the asserted parameter alone, and a
//@ mechanism: write the lane follows (a direct store) is still read at its new value. The
//@ mechanism: refusal is keyed on the asserted local's own class having a holder in it, not on any
//@ mechanism: holder in the body. The reborrow spelling moved to
//@ mechanism: v14_proof_assert_holder_write_reborrow_control.rs when D-185 refused it.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*x != 5i32)]
pub fn other_local_held(x: &mut i32) {
    let mut b = 0i32;
    let t = (&mut b, 0i32);
    *t.0 = 5i32;
    proof_assert!(*x != 5i32);
}

pub fn direct_write(x: &mut i32) {
    *x = 5i32;
    proof_assert!(*x == 5i32);
}

