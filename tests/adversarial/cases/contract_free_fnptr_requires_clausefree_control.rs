//@ expect: verify
//@ mechanism: the isolating over-refusal control for contract_free_fnptr_requires_uncharged: the
//@ mechanism: SAME clause-free host calling the SAME contracted callee through the SAME reified
//@ mechanism: `fn` pointer, with the one argument changed to one the callee's `#[requires]`
//@ mechanism: admits. Clause-free on purpose — contract_free_fnptr_requires_control carries a
//@ mechanism: contract and is therefore a verification target by the ordinary route, so it cannot
//@ mechanism: tell a discovery rule that CHARGES an indirect call from one that refuses every
//@ mechanism: body containing one. This body is a target only because the discovery predicate
//@ mechanism: treats a callee it cannot NAME as a reason to walk, and it still verifies:
//@ mechanism: `cap_clause_free_verdict` does not demote it, because `unchecked_panic_sites`
//@ mechanism: resolves the reified pointer to a local callee that carries a user spec and finds
//@ mechanism: the site accounted.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `hop verified ✓`, `3 verified, 0 failed, 0 errors`, exit 0. Its twin with the
//@ teeth: argument `0` through the identical pointer reports `hop FAILED`, so the pair separates a
//@ teeth: charge that discharges from a blanket refusal of indirect calls (D-73).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(y@ != 0u32@)]
#[ensures(result@ == 10u32@ / y@)]
pub fn need(y: u32) -> u32 {
    10u32 / y
}

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// `need`'s precondition HOLDS here, through the same function pointer.
pub fn hop() {
    let f: fn(u32) -> u32 = need;
    let _ = f(1u32);
}
