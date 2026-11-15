//@ expect: reject
//@ mechanism: the grant side of D-117. A contracted `async fn` is refused, so its `ensures` is proved by no pass, and a call to it runs none of its body, so the call is granted none of that `ensures`. A sync caller that only builds the future and was handed `ensures(false)` at the call would have every goal hold; it must be refuted on its own claim instead.
//@ accept-means: a contract no pass proves, on a refused coroutine item, discharges its caller's postcondition.
//@ WHY IT IS FALSE: `f` returns 0 and claims `result@ == 1`.
//@ teeth: rejected on the parent too, where the `ensures(false)` was still granted at the call and the vacuity check caught it (`g` refused, `f vacuous`). Now `f FAILED`: the call grants nothing, so `f` is judged on its own body. The live spellings of the same grant are async_fn_mut_param_ensures_granted_at_unpolled_call and its siblings.
//@ verdict: failed
//@ fn-failed: f
//@ refused-with: which trust-wp does not verify; refused instead of credited
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(false)]
pub async fn g() -> u32 {
    0
}

#[ensures(result@ == 1)]
pub fn f() -> u32 {
    let _fut = g();
    0
}
