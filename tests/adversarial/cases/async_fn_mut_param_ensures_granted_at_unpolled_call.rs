//@ expect: reject
//@ mechanism: the grant side of D-117. A call to an `async fn` runs none of its body: `g(&mut y)` returns a future that holds the borrow, and `drop` ends it unpolled, so `y` is still 0. The spec table handed the call `g`'s `ensures` as if the body had run, so `f` read `(^x)@ == 5` for `y`, while `g` itself was refused: the grant rested on a body no pass examined, at a call that never runs it.
//@ accept-means: a caller is credited on the postcondition of an async fn whose body its call does not run.
//@ WHY IT IS FALSE: the future is dropped unpolled, so `f` returns 0 and claims `result@ == 5`.
//@ teeth: MEASURED on the parent: `g` refused, `f verified ✓`, a false credit the per-function gate reports. At the fix `f` is not credited: the call is granted no `ensures`, which leaves a call to a contract-free `async fn`, and its lent `&mut` is refused fail-closed.
//@ fixed-by: D-117 — `ensures_granted_at_call` grants a call to an item that only builds a coroutine none of its `ensures`
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures((^x)@ == 5)]
pub async fn g(x: &mut u32) {
    *x = 5;
}

#[ensures(result@ == 5)]
pub fn f() -> u32 {
    let mut y = 0u32;
    drop(g(&mut y));
    y
}
