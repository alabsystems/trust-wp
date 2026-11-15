//@ expect: verify
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple — over-refusal control
//@ fixed-by: s34 value-carrier functional field updates
//@ accept-means: n/a (control) — this contract is TRUE.
//@ xfail: D-232 reads the clause's `+ 1u64` as the oracle's wrapping add, stated as two cases
//@ xfail: of the comparison, so the clause reads the field's final value twice; two reads of a
//@ xfail: struct field's final value already time out on their own
//@ xfail: (final_field_final_value_read_twice_control.rs).
//@ xfail-verdict: unknown
//@
//@ Same shape as s34_field_scalar_newtype with the true postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S(pub u64);

#[requires(s.0 < 100u64)]
#[ensures((^s).0 == s.0 + 1u64)]
pub fn mut_s(s: &mut S) {
    s.0 += 1;
}
