//@ expect: reject
//@ verdict: failed
//@ fn-failed: driver_fn
//@ mechanism: closure_enrichment::trivial_rewrite rewrote EVERY `__trust_wp_tuple<N>(..)`-receiver
//@ mechanism: `precondition` obligation to `true` as soon as SOME closure without `#[requires]`
//@ mechanism: existed in the body — no identity between the receiver and that closure. Here
//@ mechanism: `_c2 = |_| 2` is never even called, and the obligation it discharged is c1's
//@ mechanism: `requires(x > 0)` at `call_plain(&mut c1, -1)`.
//@ fixed-by: wp-s71 v2 — an environment receiver is rewritten only when the closure that is the
//@ fixed-by: SOLE owner of its capture arity in the body (`collect_sole_env_owners`) has no
//@ fixed-by: `#[requires]`; a name is rewritten only for a closure bound to that name.
//@ accept-means: a caller's obligation to meet a contracted closure's precondition is dropped
//@ accept-means: whenever any uncontracted closure is in scope.
//@ WHY THE CONTRACT IS FALSE: `call_plain(&mut c1, -1)` requires `c1.precondition((-1,))`, i.e.
//@ WHY THE CONTRACT IS FALSE: `-1 > 0`; `driver_fn(3)` executes exactly that call. The ensures
//@ WHY THE CONTRACT IS FALSE: `true` is there so driver_fn is verified at all; the obligation
//@ WHY THE CONTRACT IS FALSE: that must fail is the call precondition.
//@ teeth: (i) pre-fix builds ACCEPTED, exit 0 — campaign a9a5beab (ab-campaign 5d010b04 build)
//@ teeth: AND wp-s71 7b039dc3: `✓ call_plain verified / ✓ driver_fn verified / ✓ driver_fn::
//@ teeth: {closure#2} verified` — the same uncalled-sibling probe run on each of those builds.
//@ also-verified: call_plain, driver_fn::{closure#2}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires((*f).precondition((arg,)))]
#[ensures(exists<st> (*f).postcondition_mut((arg,), st, result))]
pub fn call_plain<F: FnMut(i32) -> i32>(f: &mut F, arg: i32) -> i32 {
    f(arg)
}

#[ensures(true)]
pub fn driver_fn(y: i32) -> i32 {
    let mut c1 = {
        #[requires(x > 0)]
        #[ensures(result == x)]
        move |x: i32| -> i32 {
            if x > 0 {
                x
            } else {
                y
            }
        }
    };
    let _c2 = |_x: i32| -> i32 { 2 };
    call_plain(&mut c1, -1)
}

pub fn main() {
    let _ = driver_fn(3);
}
