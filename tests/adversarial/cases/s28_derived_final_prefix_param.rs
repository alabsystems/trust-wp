//@ expect: reject
//@ mechanism: `^x` is also spelled Var("final_x") on some encoder paths; a parameter of that name aliased the prophecy.
//@ fixed-by: wp-s28 (creusot_frontend_checks::validate_derived_name_aliases)
//@ accept-means: g proved the final value of x equals an unrelated parameter.
//@ teeth: exit-0 false accept on fd776682 (rv8/dv4); renamed parameter (dv4n) not accepted.
//@ verdict: error
//@ refused-with: `final_x` is spelled as a name the verifier derives from `x`
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: final_x is an unrelated parameter.
#[ensures(^x == final_x)]
pub fn g(x: &mut u32, final_x: u32) { *x = 5; }
