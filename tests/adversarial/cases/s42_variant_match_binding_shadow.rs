//@ expect: reject
//@ mechanism: a bare match binding pattern shadowing a parameter reached the permissive Unsupported variant arm
//@ fixed-by: s42 variant-range-facts-v2
//@ accept-means: a recursive call under a parameter-shadowing match binder is accepted again
//@ timeout: 300
//@ verdict: error
//@ refused-with: logic recursion check failed: `creusot_test::f`: self-recursive logic function variant does not strictly decrease: variant `x` does not strictly decrease at self-call creusot_test::f -> creusot_test::f
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
//@ teeth: since D-100 a `match` whose first arm cannot fail is read as the `let` it spells,
//@ teeth: so `match x + 1 { x => f(x - 1) + 1 }` is `let x = x + 1; f(x - 1) + 1` and the check
//@ teeth: relates the call's argument through it, as it does s42_variant_let_shadow_int: the
//@ teeth: refusal now names the reason (the argument `(x + 1) - 1` does not decrease) instead of
//@ teeth: the shadowing. MEASURED on the D-100 tree: error with this line; on 55ffd8f7: error with
//@ teeth: the shadowing line.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn f(x: Int) -> Int {
    pearlite! { if x > 0 { match x + 1 { x => f(x - 1) + 1 } } else { 0 } }
}

#[ensures(f(1) == 42)]
pub fn g() {}
