//@ expect: reject
//@ mechanism: a clause resolves `S::C` to its last segment, so an associated const in the `__trust_wp` namespace could name a synthesized symbol; it is refused.
//@ fixed-by: wp-s28 (creusot_frontend_checks::validate_reserved_binding_names covers associated items)
//@ accept-means: an associated const spelled like a synthesized placeholder was accepted into a specification.
//@ teeth: the associated-const path class of review rv7/S2 (ac1 accepted `S::call_0` on fd776682~).
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
pub struct S;
impl S {
    #[allow(non_upper_case_globals)]
    pub const __trust_wp_fallback_arg0_0: P = P { x: 200 };
}
pub const K: P = P { x: 7 };

#[requires(v.x > 100u32)]
pub fn need(v: P) {}

// WRONG: K.x == 7 violates need's precondition.
#[requires(S::__trust_wp_fallback_arg0_0.x == 200u32)]
pub fn g() { need(K) }
