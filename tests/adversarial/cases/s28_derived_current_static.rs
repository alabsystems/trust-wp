//@ expect: reject
//@ mechanism: static twin of s28_derived_current_param.
//@ fixed-by: wp-s28 (creusot_frontend_checks::validate_derived_name_aliases covers const/static/assoc-const names)
//@ accept-means: g proved *x equals an unrelated static.
//@ teeth: static variant of rv8/dv1.
//@ verdict: error
//@ refused-with: `x_current` is spelled as a name the verifier derives from `x`
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub static x_current: u32 = 9;

// WRONG: *x is arbitrary.
#[ensures(result == x_current)]
pub fn g(x: &mut u32) -> u32 { *x }
