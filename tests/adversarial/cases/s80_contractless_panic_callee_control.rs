//@ expect: verify
//@ mechanism: over-refusal control — the caller's own claim does not rest on the panic-bearing contract-less callee's result
//@ xfail: the local opaque call is owed `requires(false)`, so every caller is unprovable today.
//@ teeth: n/a — over-refusal control. NOTE: an XPASS here is NOT unambiguously good — it means trust-wp credited a caller of a contract-less callee whose `assert!` is posed nowhere (s26 / panic-site lane). Read it together with `x_contractless_false_assert`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

fn checked_half(x: u32) -> u32 {
    assert!(x % 2 == 0, "odd");
    x / 2
}

// TRUE: caller_ok(a) returns a for every a.
#[ensures(result@ == a@)]
pub fn caller_ok(a: u32) -> u32 {
    let _ignored = checked_half(4);
    a
}
