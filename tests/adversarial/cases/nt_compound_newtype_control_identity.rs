//@ expect: verify
//@ mechanism: control for the nt_compound_newtype_* family: build_newtype_param_set must treat a
//@ mechanism: compound single-field struct (field is Vec / tuple) the same on the parameter and the
//@ mechanism: result side. Collapsing only the result compared a struct with its field, so these true
//@ mechanism: identity postconditions were unknown/refuted (wp-s11 review item 2).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W(pub Vec<u64>);
pub struct Tp(pub (u64, u64));

#[ensures(result.0@ == w.0@)]
pub fn id_view(w: W) -> W {
    w
}

#[ensures(result.0@.len() == w.0@.len())]
pub fn id_len(w: W) -> W {
    w
}

#[ensures(result.0 == t.0)]
pub fn id_tuple(t: Tp) -> Tp {
    t
}

#[requires(i@ < w.0@.len())]
#[ensures(result == w.0@[i@])]
pub fn get(w: &W, i: usize) -> u64 {
    w.0[i]
}
