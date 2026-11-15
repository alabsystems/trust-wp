//@ expect: verify
//@ xfail: `Byte` is an alias of `u8`, and a clause spelling it as a type is refused (D-205): the
//@ xfail: parser does not read a type name through Rust's scopes, so it cannot state `u8`'s range.
//@ xfail: Before D-205 the binder was read unbounded and the true contract refuted.
//@ mechanism: control: with `type Byte = u8;` no `Byte` reaches 256, and `f` returns false. The
//@ mechanism: isolating twin of quantifier_binder_module_alias_of_machine_int_read_unbounded_granted.rs.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `f FAILED ✗ (postcondition)` with D-204 in force,
//@ teeth: refused with D-205)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub type Byte = u8;

#[ensures(result == (exists<x: Byte> x@ >= 256))]
pub fn f() -> bool {
    false
}
