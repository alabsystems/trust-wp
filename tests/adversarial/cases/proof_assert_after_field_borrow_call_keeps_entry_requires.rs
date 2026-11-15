//@ expect: reject
//@ mechanism: s48_uncontracted_helper_param_field_direct.rs's defect with a contracted helper. A `&mut` borrow of a field of a BY-VALUE struct parameter goes to `set7`, whose contract says nothing about the final value, and the assertion after the call is still discharged by the precondition `p.a@ == 3` about the entry value. In s48_uncontracted_helper_param_field_direct the helper is uncontracted, so the function-level lane refuses `k` and the false `verified ✓` on its assertion is hidden behind that refusal. Give the helper `#[ensures(true)]` and nothing refuses. The same write into a local struct's field, or into a by-value scalar parameter, is refuted.
//@ accept-means: a precondition about a by-value parameter's field outlives a call that overwrote the field, and the crate exits 0.
//@ WHY THE ASSERTION IS FALSE: `set7` stores 7 into `p.a`; the assertion claims 3.
//@ teeth: MEASURED ACCEPTED, exit 0: `proof_assert in creusot_test::k verified ✓` and `k verified ✓`. With `#[ensures((^q)@ == 7)]` on the helper the assertion is refuted, because the final value is then pinned; the defect needs a callee contract that is silent on it. The control borrows the other field.
//@ fixed-by: D-241: a `&mut` borrow of the parameter's field reaches its own storage before the assertion, so its `#[requires]` is withdrawn there.
//@ also-verified: set7
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: u32,
    pub b: u32,
}

#[ensures(true)]
pub fn set7(q: &mut u32) {
    *q = 7;
}

#[requires(p.a@ == 3)]
#[ensures(true)]
pub fn k(mut p: P) -> u32 {
    set7(&mut p.a);
    proof_assert!(p.a@ == 3);
    0
}
