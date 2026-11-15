//@ expect: reject
//@ mechanism: static twin of s28_synth_const_fallback_arg: a static spelled like the old placeholder is refused.
//@ fixed-by: wp-s28 (creusot_frontend_checks::validate_reserved_binding_names covers every item kind)
//@ accept-means: need(K)'s precondition was discharged by a fact about an unrelated static.
//@ teeth: same shape as review rv7/d1_0 with `static` instead of `const`.
//@ verdict: error
//@ refused-with: item `__trust_wp_fallback_arg0_0` lies in a namespace the verifier synthesizes names in
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub x: u32,
}
pub const K: P = P { x: 7 };
#[allow(non_upper_case_globals)]
pub static __trust_wp_fallback_arg0_0: P = P { x: 200 };

#[requires(v.x > 100u32)]
pub fn need(v: P) {}

// WRONG: K.x == 7 violates need's precondition.
#[requires(__trust_wp_fallback_arg0_0.x == 200u32)]
pub fn g() { need(K) }
