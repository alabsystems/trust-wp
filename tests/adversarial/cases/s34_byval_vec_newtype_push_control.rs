//@ expect: verify
//@ xfail: completeness — a mutating call through a field borrow of an arity-1 by-value owner havocs the owner
//@ mechanism: stale by-value local after a field write — over-refusal control
//@ fixed-by: s34 functional update of by-value locals on projected writes
//@ accept-means: n/a (control) — this contract is TRUE.
//@
//@ Same shape as s34_byval_vec_newtype_push with the true postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W(pub Vec<u64>);

#[requires(w.0@.len() < 100)]
#[ensures(result.0@.len() == w.0@.len() + 1)]
pub fn param_vec_newtype_push(mut w: W) -> W {
    w.0.push(7);
    w
}
