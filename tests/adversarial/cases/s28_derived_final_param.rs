//@ expect: reject
//@ mechanism: `^x` is Var("x_final"); a parameter of that name aliased the prophecy.
//@ fixed-by: wp-s28 (creusot_frontend_checks::validate_derived_name_aliases)
//@ accept-means: g proved the final value of x equals an unrelated parameter.
//@ teeth: exit-0 false accept on fd776682 (rv8/dv2); renamed parameter (dv2n) not accepted.
//@ verdict: error
//@ refused-with: `x_final` is spelled as a name the verifier derives from `x`
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: x_final is an unrelated parameter.
#[ensures(^x == x_final)]
pub fn g(x: &mut u32, x_final: u32) { *x = 5; }
