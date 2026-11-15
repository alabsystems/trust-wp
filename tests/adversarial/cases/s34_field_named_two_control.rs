//@ expect: verify
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple — over-refusal control
//@ fixed-by: s34 value-carrier functional field updates
//@ accept-means: n/a (control) — this contract is TRUE.
//@
//@ Same shape as s34_field_named_two with the true postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub a: u64,
    pub b: u64,
}

#[requires(p.a < 100u64)]
#[ensures((^p).a == p.a + 1u64)]
#[ensures((^p).b == p.b)]
pub fn mut_p(p: &mut P) {
    p.a += 1;
}
