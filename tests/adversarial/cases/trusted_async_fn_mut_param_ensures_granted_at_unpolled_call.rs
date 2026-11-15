//@ expect: reject
//@ mechanism: the `#[trusted]` spelling of async_fn_mut_param_ensures_granted_at_unpolled_call. The trusted contract is TRUE of `g`'s body, which does leave `*x == 5` when it runs; what is false is reading it as a fact of the call, which runs none of that body. Trusting a contract assumes it of the body it describes, not of a call that only builds a future.
//@ accept-means: a trusted async fn's postcondition is granted at a call that does not run its body.
//@ WHY IT IS FALSE: the future is dropped unpolled, so `f` returns 0 and claims `result@ == 5`.
//@ teeth: MEASURED on the parent: `g trusted (skipped)`, `f verified ✓`; the run exits 2 only for the trusted item. At the fix `f` is not credited.
//@ fixed-by: D-117 — `ensures_granted_at_call` grants a call to an item that only builds a coroutine none of its `ensures`, trusted or not
//@ verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
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
