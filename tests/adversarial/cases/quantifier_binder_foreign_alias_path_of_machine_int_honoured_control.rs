//@ expect: verify
//@ xfail: `core::ffi::c_uchar` is a path through a crate, and a clause spelling one as a type is
//@ xfail: refused (D-206): the parser does not read a path to the item it names, so it cannot state
//@ xfail: `u8`'s range. Before D-206 the binder was read unbounded and the true contract refuted.
//@ mechanism: control: no `core::ffi::c_uchar` reaches 256, and `f` returns false. The isolating
//@ mechanism: twin of quantifier_binder_foreign_alias_path_of_machine_int_read_unbounded_granted.rs.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `f FAILED ✗ (postcondition)` with D-205 in force,
//@ teeth: refused with D-206)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (exists<x: core::ffi::c_uchar> x@ >= 256))]
pub fn f() -> bool {
    false
}
