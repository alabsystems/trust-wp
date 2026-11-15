//@ expect: verify
//@ mechanism: control: the same closure contract with no local `k` in the enclosing body: `k()` is the
//@ mechanism: crate root's logic function (10) and the closure returns 10. A refusal of
//@ mechanism: closure_contract_local_closure_call_granted.rs must be keyed on the local binding, not on
//@ mechanism: the closure.
//@ fixed-by: n/a (control for closure_contract_local_closure_call_granted.rs; verified before D-195 and
//@ fixed-by: with it)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> u32 {
    pearlite! { 10u32 }
}

pub fn host() -> u32 {
    let c = #[ensures(result == k())]
    || -> u32 { 10 };
    c()
}
