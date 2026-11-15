//@ expect: verify
//@ xfail: D-174 refuses a name an enclosing body redeclares rather than resolving it to the block's
//@ xfail: item, so the closure, which returns the block's `k` (0) as its contract says, is refused,
//@ xfail: not proved (D-174's price). The isolating twin of
//@ xfail: closure_contract_block_local_logic_fn_granted.rs (one literal differs).
//@ mechanism: control: the closure returns 0, which is the block's `k()`, the function its contract names.
//@ fixed-by: OPEN — resolving block scopes as Rust does (see closure_contract_block_local_logic_fn_granted.rs)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 10 }
}

pub fn host() -> u32 {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 0 }
    }
    let c = #[ensures(result@ == k())]
    || -> u32 { 0 };
    c()
}
