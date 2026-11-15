//@ expect: reject
//@ mechanism: a quantifier binder `x_current` captures the encoder's Var("x_current") for `*x`; the spec-identifier check exempted it because a local `fn x_current` shared the name. A binder is a value, so the exemption now needs every occurrence in item position.
//@ fixed-by: wp-s28 v9 (validate_derived_name_aliases item-position exemption)
//@ accept-means: g proved every u32 equals *x.
//@ teeth: unknown (not refused) on 8c8fa32f and 279f88a0 (review-probes/rv9-before/d3); without the fn item it was already refused (d3c).
//@ verdict: error
//@ refused-with: `x_current` is spelled as a name the verifier derives from `x`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn x_current() {}

#[ensures(forall<x_current: u32> x_current == *x)]
pub fn g(x: &mut u32) {}
