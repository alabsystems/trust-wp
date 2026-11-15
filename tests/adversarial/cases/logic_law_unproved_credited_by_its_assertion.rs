//@ expect: reject
//@ mechanism: a free law's postcondition is exposed unproved in non-strict mode (`assumes_concrete_law_postcondition`: `law postcondition unverified`), so its ensures lane does not run; D-106 then GRANTS the function `verified ✓` once its body assertions are proved (`logic_fn_verify.rs`: `if !ensures_lane_runs { .. grant_function_credit .. }`). The run prints the law unverified and verified two lines apart, and the credit claims a postcondition nobody proved.
//@ accept-means: a law whose postcondition is false for every argument is credited `verified` because an unrelated assertion in its body holds.
//@ WHY IT IS FALSE: `x == x + 1` holds for no `x`.
//@ teeth: MEASURED with D-106: `bad_law law postcondition unverified (non-strict axiom exposure)`, `proof_assert in creusot_test::bad_law verified ✓`, then `creusot_test::bad_law verified ✓`; the crate exits 2 on the unverified axiom, so the defect is the per-function credit, which the corpus reads as a false credit on a case whose contract is false. The same law without its assertion gets no credit line with D-106, and this very file gets none on the commit before D-106 (MEASURED: the unverified line, nothing verified, exit 2), where it reads as the named refusal it declares.
//@ verdict: error
//@ refused-with: bad_law postcondition FAILED (logic postcondition)
//@ also-verified-assertion: creusot_test::bad_law
//@ fixed-by: D-154 — a law is proved like any logic function, so its ensures lane runs and refutes `x == x + 1`; the assertion `x == x` is true and is credited on its own
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(law)]
#[ensures(x == x + 1)]
pub fn bad_law(x: Int) {
    proof_assert!(x == x);
}
