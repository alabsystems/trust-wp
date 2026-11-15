//@ expect: verify
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple — over-refusal control
//@ fixed-by: s34 value-carrier functional field updates
//@ accept-means: n/a (control) — this contract is TRUE.
//@
//@ Same shape as s34_field_vec_field_push with the true length postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct V {
    pub v: Vec<u64>,
}

#[ensures((^w).v@.len() == w.v@.len() + 1)]
pub fn push_v(w: &mut V) {
    w.v.push(1);
}
