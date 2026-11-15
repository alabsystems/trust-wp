//@ expect: reject
//@ mechanism: a spec quantifier binder `a: &mut u32` derives Var("a_current") for `*a`; the parameter `a_current` was not checked because spec binders were not bases.
//@ fixed-by: wp-s28 v9 (value-position spec identifiers are bases)
//@ accept-means: g proved every &mut u32 points at the unrelated parameter.
//@ teeth: not measured before the fix; refused after it (review-probes/rv9-after/d6).
//@ verdict: error
//@ refused-with: `a_current` is spelled as a name the verifier derives from `a`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(forall<a: &mut u32> *a == a_current)]
pub fn g(a_current: u32) {}
