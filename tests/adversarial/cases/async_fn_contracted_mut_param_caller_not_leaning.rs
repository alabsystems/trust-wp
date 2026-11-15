//@ expect: reject
//@ mechanism: the twin of async_fn_contracted_mut_param_leaning_caller_refuted that does not lean on `g`'s `ensures`: the same `g` and the same call, and `f` claims only what it returns. The call owes `g`'s `requires` (met, `y` is 0) and grants nothing, and `f` keeps its TRUE credit, so the grant fix refuses no caller wholesale.
//@ accept-means: a contracted async fn is credited, although no lane verifies a coroutine body.
//@ WHY IT IS FALSE: `g`'s `ensures` is false of its body, which writes 5, not 6.
//@ teeth: rejected on the parent too (`g` refused). MEASURED at the fix: `g` refused and `f verified ✓`, the credit declared below.
//@ fixed-by: n/a (the credit side of a pair; rejected on the parent as well)
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: f
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

#[ensures(result@ == 3)]
pub fn f() -> u32 {
    let mut y = 0u32;
    drop(g(&mut y));
    3
}
