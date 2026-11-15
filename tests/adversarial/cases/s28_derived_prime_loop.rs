//@ expect: reject
//@ mechanism: the loop next state of `n` is Var("n_prime"); a parameter of that name made the preservation obligation trivial.
//@ fixed-by: wp-s28 (creusot_frontend_checks::validate_derived_name_aliases)
//@ accept-means: g proved 10 <= an arbitrary parameter.
//@ teeth: exit-0 false accept on fd776682 (rv8/dv6); renamed parameter (dv6n) FAILED (loop invariant).
//@ verdict: error
//@ refused-with: `n_prime` is spelled as a name the verifier derives from `n`
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: n_prime is an unrelated parameter (preservation fails for n_prime < 10).
#[ensures(result <= n_prime)]
pub fn g(n_prime: u32) -> u32 {
    let mut n = 0u32;
    #[invariant(n <= n_prime)]
    #[invariant(n <= 10u32)]
    while n < 10u32 {
        n += 1;
    }
    n
}
