//@ expect: reject
//@ mechanism: the Int-variant decrease obligation ASSUMED `0 <= variant` as a hypothesis, so the
//@ mechanism: first conjunct of Creusot's well_founded_relation_Int was never proved
//@ fixed-by: s18 (variant.rs prove_self_variant_decrease: `before >= 0` is a goal only)
//@ accept-means: a logic fn whose variant goes negative is accepted with an inconsistent axiom
//@
//@ WHY IT MUST BE REJECTED: Creusot's variant goal `x <> 0 -> x >= 0 /\ x > -x` is false at
//@ x = -1. osc(1) and osc(-1) never terminate; unfolding the defining axiom twice gives
//@ osc(1) = osc(-1) + 1 = osc(1) + 2, i.e. 0 = 2. Creusot rejects the crate.
//@ teeth: VERIFIED — accepted (code 0, logic_recursion_errors 0) on ce6a788, rejected after the fix.
//@ verdict: error
//@ refused-with: logic recursion check failed: `creusot_test::osc`: self-recursive logic function variant does not strictly decrease: variant `x` does not strictly decrease at self-call creusot_test::osc -> creusot_test::osc
//@ teeth-credit: wp-s47 v2 — the rejection is this named trust-wp refusal (measured identical at edition 2021 and 2024); before, any error incl. a rustc compile error was credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
#[variant(x)]
pub fn osc(x: Int) -> Int {
    if x != 0 { osc(-x) + 1 } else { 0 }
}

pub fn uses_osc() {
    proof_assert! { osc(1) == osc(-1) + 1 };
}
