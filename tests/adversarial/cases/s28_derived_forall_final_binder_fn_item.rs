//@ expect: reject
//@ mechanism: a quantifier binder `x_final` captures the encoder's Var("x_final") for `^x`; a local `fn x_final` exempted the spec identifier.
//@ fixed-by: wp-s28 v9 (validate_derived_name_aliases item-position exemption)
//@ accept-means: g proved every u32 equals ^x.
//@ teeth: unknown (not refused) on 8c8fa32f and 279f88a0 (review-probes/rv9-before/d4).
//@ verdict: error
//@ refused-with: `x_final` is spelled as a name the verifier derives from `x`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn x_final() {}

#[ensures(forall<x_final: u32> x_final == ^x)]
pub fn g(x: &mut u32) {
    *x = 3u32;
}
