//@ expect: reject
//@ verdict: error
//@ refused-with: binding `__trust_wp_ghost_value` lies in a namespace the verifier synthesizes names in
//@ mechanism: `__trust_wp_ghost_value` was exempt from the reserved-prefix refusal for ANY macro expansion; the exemption now requires a macro defined in trust_wp_macros.
//@ fixed-by: wp-s28 v8 (is_macro_emitted checks the expansion def site)
//@ accept-means: a user macro_rules! bound a reserved synthesized name without refusal.
//@ teeth: exit 2 with the reserved-namespace refusal on v8; the contract is also false.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

macro_rules! sneaky {
    ($e:expr) => {
        let __trust_wp_ghost_value = $e;
    };
}

// WRONG: result is 1, not 2
#[ensures(result == 2u32)]
pub fn g() -> u32 { sneaky!(2u32); 1u32 }
