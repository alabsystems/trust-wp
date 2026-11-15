//@ expect: reject
//@ verdict: failed
//@ mechanism: THREE identity-free credit paths, all removed by wp-s71 v2: (1) the driver's
//@ mechanism: closure_enrichment::try_inject_concrete_ensures fell back to the SINGLE
//@ mechanism: `closure_ensures` entry when the postcondition_mut receiver matched none;
//@ mechanism: (2) forall_enrichment did the same for forall obligations; (3) LIVE ON CAMPAIGN:
//@ mechanism: trust-wp-ay's find_body_for_receiver bound a closure-ENVIRONMENT receiver
//@ mechanism: (`__trust_wp_tuple0()`, which both capture-less closures lower to) to the unique
//@ mechanism: ensures-bearing registered body (#2668), so the call on the UNCONTRACTED sibling
//@ mechanism: c2 (returns 2) was given c1's `#[ensures(result == 1)]`. `proof_assert!(r == 1)` verified for r == 2 through the
//@ mechanism: `BinOp::Implies` arm (`f.precondition(arg) ==> exists<st> ..`).
//@ fixed-by: wp-s71 v2 — an ensures / body is attached only to the closure that OWNS the
//@ fixed-by: receiver: a source-local name bound to exactly one entry, the state variable a call
//@ fixed-by: on such a closure produced, or an environment constructor whose capture arity
//@ fixed-by: exactly one closure of the body has (`collect_sole_env_owners`); otherwise nothing.
//@ accept-means: the Implies arm again grounds an existential with a sibling's contract.
//@ WHY THE CONTRACT IS FALSE: r == call_guarded(&mut c2, 0) == c2(0) == 2; `r == 1` is false.
//@ WHY THE CONTRACT IS FALSE: The callee is #[trusted] (exit 2 regardless); the proof_assert
//@ WHY THE CONTRACT IS FALSE: verdict is what this case pins.
//@ teeth: (i) pre-fix build wp-s71 75f19abf: `✓ proof_assert in driver_fn verified`,
//@ teeth: `proof_assert: 1 verified, 0 failed, 0 errors` on the sibling-mismatch probe
//@ teeth: (the Implies spelling). Campaign refused the flat spelling at spec_tc (E0282).
//@ also-verified: driver_fn::{closure#1}
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

pub fn driver_fn() {
    let mut c1 = #[requires(true)]
    #[ensures(result == 1)]
    |_x: i32| -> i32 { 1 };
    let mut c2 = |_x: i32| -> i32 { 2 };
    let _ = call_guarded(&mut c1, 0);
    let r = call_guarded(&mut c2, 0);
    proof_assert!(r == 1);
}

pub fn main() {
    driver_fn();
}
