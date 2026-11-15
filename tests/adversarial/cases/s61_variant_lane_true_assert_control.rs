//@ expect: verify
//@ mechanism: over-refusal control for s61_variant_lane_pa_false — a terminating recursive `#[variant]` function whose `proof_assert!` is TRUE (`n != 0` on that arm). Examining the assertion must not mean refuting it.
//@ xfail: the assertion is now EXAMINED (wp-s61) and refuted, twice over, by two defects that are older than wp-s61 and live on paths it does not touch. (1) The function-level VC carries `(!(n == 0) ==> false)`: `effective_user_specs_for_extraction` (parsing/extraction.rs:423) registers a self-spec for a recursive fn only when `requires` or `ensures` is non-empty, so with a `variant` clause alone the self-call is unmodelled and its arm is charged the fail-closed `false`. (2) The in-function assertion pass refutes `n > 0` with the model `n = -1`, outside u32. Campaign 04fc8074 "verified" this crate only because NO lane examined either obligation.
//@ fixed-by: n/a — this control is the honest record of what closing the false accept costs.
//@ teeth: exit 0 on wp-campaign 04fc8074 with `1 verified, 0 failed, 0 errors` and proof_assert_verified=0 — a vacuous pass (A/B 2026-09-14, <session-scratch>/ab.log)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[variant(n)]
pub fn countdown5(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        proof_assert!(n > 0u32);
        countdown5(n - 1)
    }
}
