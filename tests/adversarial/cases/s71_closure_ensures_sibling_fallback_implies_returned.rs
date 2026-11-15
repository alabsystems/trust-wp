//@ expect: reject
//@ verdict: unknown
//@ mechanism: THREE identity-free credit paths, all removed by wp-s71 v2: (1) the driver's
//@ mechanism: closure_enrichment::try_inject_concrete_ensures fell back to the SINGLE
//@ mechanism: `closure_ensures` entry when the postcondition_mut receiver matched none;
//@ mechanism: (2) forall_enrichment did the same for forall obligations; (3) LIVE ON CAMPAIGN:
//@ mechanism: trust-wp-ay's find_body_for_receiver bound a closure-ENVIRONMENT receiver
//@ mechanism: (`__trust_wp_tuple0()`, which both capture-less closures lower to) to the unique
//@ mechanism: ensures-bearing registered body (#2668), so the call on the UNCONTRACTED sibling
//@ mechanism: c2 (returns 2) was given c1's `#[ensures(result == 1)]`, reached through the
//@ mechanism: `BinOp::Implies` arm (`f.precondition(arg) ==> exists<st> ..`), and driver_fn's
//@ mechanism: own `#[ensures(result == 1)]` verified from it.
//@ fixed-by: wp-s71 v2 — an ensures / body is attached only to the closure that OWNS the
//@ fixed-by: receiver: a source-local name bound to exactly one entry, the state variable a call
//@ fixed-by: on such a closure produced, or an environment constructor whose capture arity
//@ fixed-by: exactly one closure of the body has (`collect_sole_env_owners`); otherwise nothing.
//@ accept-means: a function-level ensures is again discharged from a sibling closure's contract.
//@ WHY THE CONTRACT IS FALSE: driver_fn() == c2(0) == 2, not 1 (main asserts it). The callee
//@ WHY THE CONTRACT IS FALSE: is #[trusted], so the crate exits 2 either way — the
//@ WHY THE CONTRACT IS FALSE: `driver_fn` verdict is what this case pins.
//@ teeth: (i) pre-fix build wp-s71 75f19abf: `✓ driver_fn verified / 2 verified, 0 failed,
//@ teeth: 0 errors, 1 trusted` (review probe p2i_implies_returned) —
//@ teeth: a wrong verdict hidden behind the soundness-gap exit, not a caught one.
//@ also-verified: driver_fn::{closure#2}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[trusted]
#[requires((*f).precondition(arg))]
#[ensures((*f).precondition(arg) ==> exists<st> (*f).postcondition_mut(arg, st, result))]
pub fn call_guarded<F: FnMut(i32) -> i32>(f: &mut F, arg: i32) -> i32 {
    f(arg)
}

#[ensures(result == 1)]
pub fn driver_fn() -> i32 {
    let mut c1 = #[requires(true)]
    #[ensures(result == 1)]
    |_x: i32| -> i32 { 1 };
    let mut c2 = |_x: i32| -> i32 { 2 };
    let _ = call_guarded(&mut c1, 0);
    call_guarded(&mut c2, 0)
}

pub fn main() {
    assert_eq!(driver_fn(), 2);
}
