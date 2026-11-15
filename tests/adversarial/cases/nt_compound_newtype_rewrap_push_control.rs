//@ expect: verify
//@ mechanism: end-to-end control for nt_compound_newtype_rewrap_push_*: the TRUE contract for rebuilding W(v) after a push
//@ accept-means: n/a (control)
//@ teeth: refused today by the compound single-field aggregate guard (25a0223); verifying it needs W(v) lowered to a constructor whose projection is v
//@ xfail: aggregate W(v) of a compound native single-field struct is refused fail-closed until the body lowering keeps the projection
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W(pub Vec<u64>);

#[requires(w.0@.len() < 100)]
#[ensures(result.0@.len() == w.0@.len() + 1)]
pub fn rewrap_push(w: W) -> W {
    let mut v = w.0;
    v.push(7);
    W(v)
}
