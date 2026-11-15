//@ expect: reject
//@ mechanism: the encoder names `*x` Var("x_current"); a parameter named `x_current` next to `x: &mut u32` was the same solver constant. The source name is refused.
//@ fixed-by: wp-s28 (creusot_frontend_checks::validate_derived_name_aliases)
//@ accept-means: g proved its result equals an unrelated parameter.
//@ teeth: exit-0 false accept on fd776682 (rv8/dv1); renamed parameter (dv1n) not accepted.
//@ verdict: error
//@ refused-with: `x_current` is spelled as a name the verifier derives from `x`
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: x_current is an unrelated parameter.
#[ensures(result == x_current)]
pub fn g(x: &mut u32, x_current: u32) -> u32 { *x }
