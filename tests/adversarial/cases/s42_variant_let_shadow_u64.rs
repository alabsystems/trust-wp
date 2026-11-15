//@ expect: reject
//@ mechanism: let-shadowing a parameter was not binder-aware in the recursion call-edge collector
//@ fixed-by: s42 variant-range-facts-v2
//@ accept-means: let x = x + 1; f(x - 1) was checked as f(x - 1): let values are no longer substituted into call edges
//@ timeout: 300
//@ verdict: error
//@ refused-with: logic recursion check failed: `creusot_test::f`: self-recursive logic function variant decrease could not be proven: the body could not be parsed
//@ mechanism: Under D-232 the body applies `+` at `u64` and at `Int`, which is refused before the
//@ mechanism: recursion check reads it; s42_variant_let_shadow_u64_machine_ops_only.rs keeps that
//@ mechanism: check's teeth with machine-integer operators alone.
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn f(x: u64) -> Int {
    pearlite! { if x > 0u64 { let x = x + 1u64; f(x - 1u64) + 1 } else { 0 } }
}

#[ensures(f(1u64) == 42)]
pub fn g() {}
