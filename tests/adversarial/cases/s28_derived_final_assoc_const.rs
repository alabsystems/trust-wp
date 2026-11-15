//@ expect: reject
//@ mechanism: associated-const twin of s28_derived_final_param (`S::x_final` resolves to `x_final`).
//@ fixed-by: wp-s28 (creusot_frontend_checks::validate_derived_name_aliases covers associated consts)
//@ accept-means: g proved the final value of x equals an associated const.
//@ teeth: associated-const variant of rv8/dv2.
//@ verdict: error
//@ refused-with: `x_final` is spelled as a name the verifier derives from `x`
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S;
impl S {
    #[allow(non_upper_case_globals)]
    pub const x_final: u32 = 9;
}

// WRONG: ^x is 5.
#[ensures(^x == S::x_final)]
pub fn g(x: &mut u32) { *x = 5; }
