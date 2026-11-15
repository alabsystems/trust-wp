//@ expect: reject
//@ mechanism: the contract-free spelling of async_fn_body_overflow_never_examined. That case is closed because the contract loop refuses a CONTRACTED `async fn` item. A contract-free `async fn` is admitted by nothing: its item's HIR walk stops at the desugared coroutine (`ExprKind::Closure => return`), and the coroutine body itself is excluded by `has_arithmetic_panic_sites` (`coroutine_kind().is_some()` -> false). The same function without `async` is examined and its overflow reported. `zero` is beside it so that the run examines something.
//@ accept-means: a contract-free `async fn` whose body overflows is examined by no pass and the crate exits 0.
//@ WHY IT IS FALSE: at `x == 1`, `x + u32::MAX` overflows; Creusot owes the `+` precondition in every program function, contracted or not.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-106 and on the commit before it: `zero verified ✓` and no line for `f`. The sync twin (the same file without `async`) is rejected: `f unknown`, exit 1. REFUSED at D-117: `f::{closure#0} error: ... refused instead of credited`.
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub async fn f(x: u32) -> u32 {
    x + u32::MAX
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
