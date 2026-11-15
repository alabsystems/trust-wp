//@ expect: verify
//@ mechanism: over-refusal control for contract_free_closure_call_uncharged: the same
//@ mechanism: contract-free closure behind the same generic `Fn` hop, with the hop passing an
//@ mechanism: argument its callee's precondition admits. This contract is TRUE, so it must
//@ mechanism: verify; a fix that charges the call site must keep it verifying rather than
//@ mechanism: refusing every closure that reaches a contracted function.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control; verifies today (exit 0, `3 verified, 0 failed, 0 errors`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x != 0i32)]
#[ensures(result@ == 10i32@ / x@)]
pub fn needs_nonzero(x: i32) -> i32 {
    10i32 / x
}

#[requires(f.precondition((2i32,)))]
pub fn call_with_two<F: Fn(i32) -> i32>(f: F) -> i32 {
    f(2i32)
}

#[ensures(result@ == result@)]
pub fn good() -> i32 {
    let c = |x: i32| needs_nonzero(x);
    call_with_two(c)
}
