//@ expect: verify
//@ mechanism: control for s28_derived_old_view_current: a correct `old(*view)` contract on a parameter literally named `view` must still verify (the base `view` itself is never refused).
//@ fixed-by: wp-s28 v9 (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*view < 100u32)]
#[ensures(*view == old(*view) + 1u32)]
pub fn g(view: &mut u32) {
    *view = *view + 1u32;
}
