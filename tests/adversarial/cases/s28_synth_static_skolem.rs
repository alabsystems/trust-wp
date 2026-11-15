//@ expect: reject
//@ mechanism: static twin of s28_synth_skolem_param: the negated universal goal skolemized
//@ mechanism: `forall<i>` to Var("sk_i"), the same solver symbol as a static named `sk_i`.
//@ fixed-by: wp-s28 (trust-wp-ay skolem names in the `$` namespace)
//@ accept-means: g proved every u32 equals a static.
//@ teeth: wp-s47 v2 repair. The previous body-less `pub fn g() {}` was `assumed (axiom-only
//@ teeth: function ...)` and never reached ay; it was rejected only by the "nothing verified" rule
//@ teeth: and scored [ok] as verdict=error, so the skolem mechanism was never exercised. `g` now
//@ teeth: takes a parameter and returns it, so the postcondition goes to ay: `g FAILED ✗ (postcondition)`.
//@ teeth: VERIFIED — with both function-postcondition skolem sites in trust-wp-ay reverted to the
//@ teeth: pre-wp-s28 `sk_{var}` spelling (result_binding.rs collect_forall_skolem_substitutions,
//@ teeth: axiom_detection.rs), this case AND s28_synth_skolem_param were ACCEPTED (`g verified ✓`,
//@ teeth: 1 verified); on the real build both are FAILED. Knob reverted, crates diff empty.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub static sk_i: u32 = 5;

// WRONG: not every i equals 5.
#[ensures(forall<i: u32> i == sk_i)]
pub fn g(x: u32) -> u32 {
    x
}
