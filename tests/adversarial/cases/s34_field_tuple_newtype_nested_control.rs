//@ expect: verify
//@ xfail: completeness — ends `unknown (proof-trusted)`: ay returns unsat but its UNSAT certificate is not strict (final value is the correct tuple1(tuple2(get_0(get_0(*t)) + 1, ..)); verified at e28ef0c4, unknown after the wp-campaign merge with and without the s34 extract commits)
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple — over-refusal control
//@ fixed-by: s34 value-carrier functional field updates
//@ accept-means: n/a (control) — this contract is TRUE.
//@
//@ Same shape as s34_field_tuple_newtype_nested with the true postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct Tp(pub (u64, u64));

#[requires(t.0.0 < 100u64)]
#[ensures((^t).0.0 == t.0.0 + 1u64)]
pub fn mut_tp(t: &mut Tp) {
    t.0.0 += 1;
}
