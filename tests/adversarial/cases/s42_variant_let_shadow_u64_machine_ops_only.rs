//@ expect: reject
//@ mechanism: let-shadowing a parameter must be binder-aware in the recursion call-edge collector:
//@ mechanism: s42_variant_let_shadow_u64 with every operator of the body on `u64`, so that D-232
//@ mechanism: reads the body (its `+` at `u64` and at `Int` is refused) and the recursion check
//@ mechanism: meets the shadowing let.
//@ accept-means: let x = x + 1; f(x - 1) was checked as f(x - 1): the let's value was not
//@ accept-means: substituted into the call edge.
//@ WHY THE CONTRACT IS FALSE: the self-call's argument is (x + 1) - 1 = x on `u64`, wrapping or
//@ WHY THE CONTRACT IS FALSE: not, so the variant does not decrease and f does not terminate.
//@ timeout: 300
//@ verdict: error
//@ refused-with: logic recursion check failed: `creusot_test::f`: self-recursive logic function variant does not strictly decrease: variant `x` does not strictly decrease at self-call creusot_test::f -> creusot_test::f
//@ teeth: UNVERIFIED: written beside D-232 after s42_variant_let_shadow_u64 stopped reaching the
//@ teeth: recursion check; it pins the shape that check refuses.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn f(x: u64) -> Int {
    pearlite! { if x > 0u64 { let x = x + 1u64; f(x - 1u64) } else { 0 } }
}

#[ensures(f(1u64) == 42)]
pub fn g() {}
