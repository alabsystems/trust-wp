//@ expect: verify
//@ mechanism: over-refusal control for s61_variant_lane_call_precondition — plain variant-only recursion with no assertion and no other call. Reaching the function-level VC must not mean failing it.
//@ xfail: the VC is now BUILT for this shape and carries `(!(n == 0) ==> false)`, refuted at n = 1. Root cause is older than wp-s61 and on a path it does not touch: `effective_user_specs_for_extraction` (parsing/extraction.rs:423) registers the self-spec only when `requires` or `ensures` is non-empty, so a `variant`-only recursive fn's self-call is unmodelled and the extractor charges its arm the fail-closed `false`. Adding `#[ensures(true)]` to this same body makes the VC UNSAT on the same build (probe p08), which is what isolates the cause. The corpus cost of both is ZERO: the 70-test variant risk surface is status-identical to campaign 04fc8074 (same-session A/B). The one verdict that moves inside a test is spans.rs `quux`, `verified (termination)` -> `FAILED (postcondition)`, on a test that is `error` on BOTH builds; its recursive call's own precondition obligation `0 <= $call_9@` is stated without the arm's path condition and fails identically on campaign once an `#[ensures]` is added (probe p09).
//@ fixed-by: n/a — followup: register an empty self-spec for a recursive fn with no requires/ensures, or state the unmodelled-call arm obligation as the callee's actual precondition.
//@ fixed-by: wp-s80 closed the named root cause — `effective_user_specs_for_extraction` now injects the self-spec for EVERY recursive function, empty contract included. MEASURED at 0bead8ec: the `(!(n == 0) ==> false)` refutation is gone and `countdown6` reports `verified (termination)` then `unknown (proof-trusted)` when run in isolation. The xfail stays because the row is still not ACCEPTED — what is left is the proof-trust withholding lane, a different owner.
//@ teeth: exit 0 on wp-campaign 04fc8074 with `1 verified, 0 failed, 0 errors` — the VC was never built (A/B 2026-09-14, <session-scratch>/ab.log)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[variant(n)]
pub fn countdown6(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        countdown6(n - 1)
    }
}
