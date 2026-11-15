//@ expect: reject
//@ mechanism: a `proof_assert!` in the body of a CONTRACTED `#[logic]` function is a goal of that function: Creusot translates it to `TermKind::Assert`, and the logic VC generator (`backend/logic/vcgen.rs`) conjoins its condition into the `vc_` goal it emits for every logic function with a contract. trust-wp's logic-postcondition lane proves `ensures` from the body's value and never looks at the assertion, the standalone pass skips logic functions, and the in-function pass runs only in the contract loop, which a logic function never enters. D-87 emits a logic function's credit at once on the premise that no in-body assertion of it is still to come; this body has one that no pass examines.
//@ accept-means: a logic function whose own assertion is false for every call is credited `verified`, and the crate exits 0.
//@ WHY THE ASSERTION IS FALSE: `false` never holds, and the function's `vc_` goal in Creusot carries it.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-87's fold and before it: `creusot_test::one verified ✓` with no assertion verdict of any kind. The same function with `proof_assert!(true)` verifies. A logic function WITHOUT a contract gets no goal in Creusot (`translate_logic` returns before building one), so that shape is not a defect and is not this case.
//@ fixed-by: D-106 — the logic lane states the body's assertions as one goal (`logic_fn_verify::assertions::assertion_goal`) under the function's own `requires`, answers it before the ensures lane may grant, and counts a refuted one as the function's failure
//@ fn-failed: creusot_test::one
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result == 1)]
pub fn one() -> Int {
    proof_assert!(false);
    1
}
