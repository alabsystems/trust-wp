//@ expect: reject
//@ verdict: error
//@ refused-with: vacuous (termination
//@ mechanism: the recursive-`#[variant]` lane swallowed a VACUOUS call-site result (recursive_verify.rs, `UnknownReason::SolverMessage("vacuous proof: base assertions are UNSAT ...")`): it only debug-logged, left `all_variants_verified` true, and the tail then printed `verified ✓ (termination)` and bumped `counters.verified`. The obligation was never decided — the DIAGNOSTIC line for `nonterm::variant_decrease[0]` carries `assertions=0 ay_result=none`.
//@ accept-means: trust-wp claims it PROVED that `nonterm` terminates. FALSE — `nonterm(x) = nonterm(x)` never terminates; nothing about its variant was decided. The unsatisfiable `#[requires]` makes the function uncallable, so this is a labelling defect rather than a live runtime unsoundness — but `verified` is the number the campaign goal is defined by, and this awards it for a proof with zero assertions.
//@ fixed-by: wp-s61 v2 — a vacuous variant site sets `any_vacuous`, and the tail takes a `vacuous` arm (`counters.vacuous`, exit 2) instead of the `verified` arm
//@ teeth: ACCEPTED, exit 0, `trust-wp: nonterm verified ✓ (termination)` with `1 verified, 0 failed, 0 errors` on wp-campaign 3dd2cf4e (measured 2026-09-14)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x > 0i32 && x < 0i32)]
#[variant(x)]
pub fn nonterm(x: i32) -> i32 {
    nonterm(x)
}
