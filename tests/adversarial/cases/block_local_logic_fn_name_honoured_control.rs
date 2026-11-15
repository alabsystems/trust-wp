//@ expect: verify
//@ xfail: D-174 refuses a name an enclosing body redeclares rather than resolving it to the block's
//@ xfail: item, so `inner`, which returns the block's `k` (0) as its contract says, is refused, not
//@ xfail: proved (D-174's price). The isolating twin of
//@ xfail: block_local_logic_fn_name_resolved_in_module_granted.rs (one literal differs). An XPASS
//@ xfail: with that case rejecting is the signal that block scopes are resolved as Rust does.
//@ mechanism: control: `inner` returns 0, which is the block's `k()`, the function its contract names.
//@ fixed-by: OPEN — resolving block scopes as Rust does (see block_local_logic_fn_name_resolved_in_module_granted.rs)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED as `host::inner FAILED ✗ (postcondition)`)
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
    #[ensures(result@ == k())]
    fn inner() -> u32 {
        0
    }
    inner()
}
