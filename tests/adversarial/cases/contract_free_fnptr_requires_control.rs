//@ expect: verify
//@ mechanism: over-refusal control for contract_free_fnptr_requires_uncharged — the same call
//@ mechanism: through the same function pointer with an argument the callee's `#[requires]`
//@ mechanism: admits. The host carries a contract deliberately: a clause-free twin would be
//@ mechanism: demoted by `cap_clause_free_verdict` the moment the hole is closed, so it could
//@ mechanism: not tell a charge that DISCHARGES from a blanket refusal of every indirect call.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — it verifies only while the fn-pointer call site is charged and discharged
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

#[ensures(result@ == 0u32@ || result@ != 0u32@)]
pub fn hop() -> u32 {
    let f: fn(u32) -> u32 = need;
    f(1u32)
}
