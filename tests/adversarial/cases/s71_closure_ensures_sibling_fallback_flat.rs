//@ expect: reject
//@ verdict: unknown
//@ mechanism: THREE identity-free credit paths, all removed by wp-s71 v2: (1) the driver's
//@ mechanism: closure_enrichment::try_inject_concrete_ensures fell back to the SINGLE
//@ mechanism: `closure_ensures` entry when the postcondition_mut receiver matched none;
//@ mechanism: (2) forall_enrichment did the same for forall obligations; (3) LIVE ON CAMPAIGN:
//@ mechanism: trust-wp-ay's find_body_for_receiver bound a closure-ENVIRONMENT receiver
//@ mechanism: (`__trust_wp_tuple0()`, which both capture-less closures lower to) to the unique
//@ mechanism: ensures-bearing registered body (#2668), so the call on the UNCONTRACTED sibling
//@ mechanism: c2 (returns 2) was given c1's `#[ensures(result == 1)]`. Flat `Fn` spelling.
//@ fixed-by: wp-s71 v2 — an ensures / body is attached only to the closure that OWNS the
//@ fixed-by: receiver: a source-local name bound to exactly one entry, the state variable a call
//@ fixed-by: on such a closure produced, or an environment constructor whose capture arity
//@ fixed-by: exactly one closure of the body has (`collect_sole_env_owners`); otherwise nothing.
//@ accept-means: an unrelated closure's contract is again assumed for a different receiver:
//@ accept-means: `driver_fn` returns 2 and `#[ensures(result == 1)]` verifies at exit 0.
//@ WHY THE CONTRACT IS FALSE: driver_fn() == call_plain(&mut c2, 0) == c2(0) == 2, not 1
//@ WHY THE CONTRACT IS FALSE: (main asserts exactly that). No #[trusted] anywhere.
//@ teeth: (i) pre-fix build ACCEPTED — wp-s71 75f19abf: `✓ call_plain verified / ✓ driver_fn
//@ teeth: verified / 3 verified, 0 failed, 0 errors`, exit 0 on the review probe of this
//@ teeth: same flat spelling; the campaign driver (a9a5beab) refused this FLAT
//@ teeth: spelling at spec_tc (E0282) — the tupled twin s71_closure_ensures_sibling_fallback_tupled
//@ teeth: is the one ACCEPTED on campaign itself.
//@ also-verified: call_plain, driver_fn::{closure#2}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires((*f).precondition(arg))]
#[ensures(exists<st> (*f).postcondition_mut(arg, st, result))]
pub fn call_plain<F: FnMut(i32) -> i32>(f: &mut F, arg: i32) -> i32 {
    f(arg)
}

#[ensures(result == 1)]
pub fn driver_fn() -> i32 {
    let mut c1 = #[requires(true)]
    #[ensures(result == 1)]
    |_x: i32| -> i32 { 1 };
    let mut c2 = |_x: i32| -> i32 { 2 };
    let _ = call_plain(&mut c1, 0);
    call_plain(&mut c2, 0)
}

pub fn main() {
    assert_eq!(driver_fn(), 2);
}
