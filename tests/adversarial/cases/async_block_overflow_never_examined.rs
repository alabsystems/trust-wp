//@ expect: reject
//@ mechanism: the arithmetic twin of async_block_assertion_never_examined. D-106 refuses a coroutine body only where a pass meets it: the contract loop meets a CONTRACTED item (`check_contract_skip` -> `CoroutineBody`) and the standalone pass meets a body holding a `proof_assert!`. An `async` block whose only obligation is arithmetic is met by neither: `has_arithmetic_panic_sites` answers false for any body with a `coroutine_kind`, so the block is never a verification target, never refused, and the crate exits 0 around an addition that overflows. async_fn_body_overflow_never_examined.rs is closed only because its `async fn` item carries a contract; the same body written as a block is not.
//@ accept-means: an addition that overflows, in a coroutine body the crate compiles, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `x == 1`, which the precondition admits, `x + u32::MAX` overflows, and Creusot's program-function precondition for `+` is owed at it.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-106 and on the commit before it: `f verified ✓` and no line for the block. The same body as a plain `move ||` closure is examined with D-106 (`unknown`, exit 1), so only the coroutine spelling escapes. REFUSED at D-117: `f::{closure#2} error: ... refused instead of credited`.
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(0 < x@ && x@ < 100)]
#[ensures(result@ == x@)]
pub fn f(x: u32) -> u32 {
    let _fut = async move { x + u32::MAX };
    x
}
