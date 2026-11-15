//@ expect: reject
//@ mechanism: the index spelling of contract_free_async_fn_overflow_never_examined. A contract-free `async fn` item only builds its coroutine, and the coroutine body — where `v[i]`'s bounds check sits — was admitted by no discovery: `fn_owes_abort_or_callee_precondition` never admits a closure-kind body and `has_arithmetic_panic_sites` excludes a coroutine, so the `Assert` was examined by nothing.
//@ accept-means: an index that can be out of bounds, in an `async fn` the crate compiles, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `i == 3` the index is out of bounds for a `[u32; 3]`, and Creusot's `index in bounds` goal is owed at it.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `zero verified ✓` and no line for the coroutine; REFUSED at the fix (`g::{closure#0} error: ... refused instead of credited`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub async fn g(v: [u32; 3], i: usize) -> u32 {
    v[i]
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
