//@ expect: verify
//@ timeout: 300
//@ mechanism: the point-write facts of a `&mut` slice parameter are read off the final value the mut-borrow
//@ mechanism: lane binds, `Ite(flag, (*a)@.set(i, 3), *a)`, one path at a time and each under its path's
//@ mechanism: conditions (`indexed_write_final_value_facts`, D-169). Before D-169,
//@ mechanism: `synthesize_indexed_write_postconditions` stated every recorded write as the unguarded premise
//@ mechanism: `(^a)@[i] == 3`, true only where `flag` holds.
//@ mechanism: control: the final value is claimed only under the condition of the arm that writes it, so the
//@ mechanism: contract is true, and a fix that guards the premise must keep it verified. Twin of
//@ mechanism: indexed_write_on_one_arm_final_value_slice.rs. The solver needs more than the default budget
//@ mechanism: under load, hence the long one.
//@ accept-means: n/a (control)
//@ teeth: n/a (control); `g FAILED (postcondition)` without D-168, whose bounds check owed the fail-closed `false`.
//@ fixed-by: n/a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(i@ < a@.len())]
#[ensures(flag ==> (^a)[i@]@ == 3)]
pub fn g(a: &mut [u32], i: usize, flag: bool) {
    if flag {
        a[i] = 3;
    }
}
