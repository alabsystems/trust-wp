//@ expect: verify
//@ mechanism: control for the contract-free discovery pass — a contract-free caller that SATISFIES
//@ mechanism: the callee's `#[requires]`. Making the caller a target must state the obligation, not
//@ mechanism: refuse the body: this separates the fix from a blanket refusal of contract-free items.
//@ teeth: control — it verifies only if the newly-stated callee precondition discharges
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(y@ != 0u32@)]
#[ensures(result@ == y@)]
pub fn need(y: u32) -> u32 {
    y
}

pub fn hop() {
    let _ = need(1u32);
}
