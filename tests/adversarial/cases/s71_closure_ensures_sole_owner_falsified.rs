//@ expect: reject
//@ verdict: failed
//@ fn-failed: driver_fn
//@ ay-not-unsat: driver_fn
//@ mechanism: the falsified twin of s71_closure_ensures_sole_owner_control.rs — that file
//@ mechanism: VERBATIM with ONE change: `driver_fn` takes `y` and returns `y` instead of the
//@ mechanism: call result, so `driver_fn(7) == 7` while the contract still claims
//@ mechanism: `result == 1`. The sole-owner identity rule still resolves the
//@ mechanism: `__trust_wp_tuple0()` receiver to c1 and c1's `#[ensures(result == 1)]` is still
//@ mechanism: inlined — correctly, because c1 IS the callee. What was broken is the BINDING of
//@ mechanism: that clause: closure_inline/mod.rs substituted its captures and pre/post state
//@ mechanism: only, leaving the clause's own `result` free, and a free `result` resolves to the
//@ mechanism: ENCLOSING function's result variable. c1's postcondition was therefore asserted
//@ mechanism: as `driver_fn's result == 1` — a fact no spec states — and the contract "proved"
//@ mechanism: itself no matter what driver_fn returns.
//@ fixed-by: wp-s71 v4 — every inlined closure clause is bound through
//@ fixed-by: substitute_closure_contract_expr (formal params AND `result` -> this call's
//@ fixed-by: arguments), the same helper the body-less ensures-only path already used; a
//@ fixed-by: binding that would be ambiguous inlines nothing and falls back to the UF encoding.
//@ accept-means: a called closure's postcondition is again assumed about the CALLER's return
//@ accept-means: value: `driver_fn(7)` returns 7 and `#[ensures(result == 1)]` verifies.
//@ WHY THE CONTRACT IS FALSE: driver_fn(7) == 7, not 1 (main asserts exactly that). The call
//@ WHY THE CONTRACT IS FALSE: result is discarded. No #[trusted] anywhere.
//@ teeth: pre-fix build ACCEPTED — wp-s71 1aa6e565 on the same source outside the corpus
//@ teeth: as a standalone review probe: `✓ call_plain
//@ teeth: verified / ✓ driver_fn verified / ✓ driver_fn::{closure#1} verified / 3 verified,
//@ teeth: 0 failed, 0 errors`, exit 0. Post-fix: `✗ driver_fn FAILED (postcondition)`, exit 1.
//@ also-verified: call_plain, driver_fn::{closure#1}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires((*f).precondition(arg))]
#[ensures(exists<st> (*f).postcondition_mut(arg, st, result))]
pub fn call_plain<F: FnMut(i32) -> i32>(f: &mut F, arg: i32) -> i32 {
    f(arg)
}

#[ensures(result == 1)]
pub fn driver_fn(y: i32) -> i32 {
    let mut c1 = {
        #[requires(true)]
        #[ensures(result == 1)]
        |_x: i32| -> i32 { 1 }
    };
    let _ = call_plain(&mut c1, 0);
    y
}

pub fn main() {
    assert_eq!(driver_fn(7), 7);
}
