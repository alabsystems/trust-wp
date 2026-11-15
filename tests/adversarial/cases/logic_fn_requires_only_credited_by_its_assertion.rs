//@ expect: reject
//@ mechanism: D-106 GRANTS `verified ✓` to a contracted logic function whose ensures lane does not run (no `ensures`, or a law exposed unproved) as soon as its body assertions are proved (`logic_fn_verify.rs`: `if !ensures_lane_runs { .. grant_function_credit .. }`). The credit is the function's verdict, but the code that grants it examined only the assertions: Creusot's `vc_` for this function also owes the precondition of every logic call in the body (`backend/logic/vcgen.rs`, `TermKind::Call`), which no trust-wp lane examines (logic_fn_callee_precondition_never_examined.rs). A `proof_assert!(true)` is therefore enough to turn a run that examined nothing into a clean accept.
//@ accept-means: a requires-only logic function that calls another outside its precondition is credited `verified` because an unrelated assertion in its body holds, and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0`, which `caller`'s precondition admits, `needs_pos(0)` violates `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-106: `proof_assert in creusot_test::caller verified ✓`, `creusot_test::caller verified ✓`. The same file without the `proof_assert!(true)` line exits 2 with D-106 (nothing verified, nothing examined), and so did this very file on the commit before D-106 (MEASURED: `caller is a logic function (definition registered)`, nothing verified, exit 2), whose logic lane skipped every function with no `ensures`: the assertion lane's grant is what accepts it. The recursive spelling (`#[requires(x > 0)] #[variant(x)]`, body `proof_assert!(x > 0); if x > 1 { f(x - 2) } else { 0 }`, which calls `f(0)` at `x == 2`) is ACCEPTED the same way.
//@ fixed-by: D-119 — a function with no `ensures` owes its callees' preconditions beside its assertions, and is credited only when both are proved; the true assertion keeps its own proof line.
//@ fn-failed: creusot_test::caller
//@ also-verified-assertion: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
#[requires(true)]
pub fn caller(y: Int) -> Int {
    proof_assert!(true);
    needs_pos(y)
}
