//@ expect: reject
//@ mechanism: a contracted `async fn` that keeps a `requires` after the call loses its `ensures`: the call still owes the precondition and is modelled as a call to a spec-bearing callee whose postcondition says nothing, so the lent `&mut`'s final value is unconstrained. Its twin async_fn_contracted_mut_param_caller_not_leaning differs only in `f`'s claim and keeps `f`'s credit, so the call is not refused wholesale; only the grant is gone.
//@ accept-means: a caller is credited on the postcondition of an async fn whose body its call does not run.
//@ WHY IT IS FALSE: `g`'s `ensures` is false of its body (it writes 5, not 6), and the future is dropped unpolled, so `f` returns 0 and claims `result@ == 6`.
//@ teeth: MEASURED on the parent: `g` refused, `f verified ✓`. At the fix: `f FAILED`.
//@ fixed-by: D-117 — `ensures_granted_at_call` grants a call to an item that only builds a coroutine none of its `ensures`
//@ verdict: failed
//@ fn-failed: f
//@ refused-with: which trust-wp does not verify; refused instead of credited
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*x)@ < 10)]
#[ensures((^x)@ == 6)]
pub async fn g(x: &mut u32) {
    *x = 5;
}

#[ensures(result@ == 6)]
pub fn f() -> u32 {
    let mut y = 0u32;
    drop(g(&mut y));
    y
}
