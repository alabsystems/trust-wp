//@ expect: reject
//@ mechanism: the placeholder for an untranslatable call argument was Var("__trust_wp_fallback_arg0_0"); a const of that name resolved to the same solver symbol,
//@ mechanism: so a requires over the const discharged the callee precondition. Placeholders are now `$fallback_argI_N`; the const is refused (`__trust_wp` prefix).
//@ fixed-by: wp-s28 (synthesized_names `$` namespace; creusot_frontend_checks::validate_reserved_binding_names)
//@ accept-means: need(K)'s precondition v.x > 100 was discharged although K.x == 7.
//@ teeth: exit-0 false accept on c030a10d (review rv7/d1_0); FAILED at 3eede3c2.
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
pub const __trust_wp_fallback_arg0_0: P = P { x: 200 };

#[requires(v.x > 100u32)]
pub fn need(v: P) {}

// WRONG: K.x == 7 violates need's precondition.
#[requires(__trust_wp_fallback_arg0_0.x == 200u32)]
pub fn g() { need(K) }
