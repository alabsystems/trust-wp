//@ expect: verify
//@ xfail: the contract-free body is now a verification target, and `cap_clause_free_verdict`
//@ xfail: then demotes its clause-free `verified` to `unknown (partial: panic paths
//@ xfail: unchecked)`. The cap counts a call to a callee with a builtin std spec as an
//@ xfail: unaccounted panic site even though the call lane charges that spec's `requires`,
//@ xfail: and it counts an `assert!` arm the switch lane has just charged. An XPASS here is
//@ xfail: the signal that the cap learned to read what the extraction lane actually charged.
//@ mechanism: over-refusal control for the wp-s71 v2 identity rule on closure-ENVIRONMENT
//@ mechanism: receivers: c1 is built inside a block (it lands in a temporary, so it has no
//@ mechanism: source name) and is the ONLY closure of arity 0 in the body, so
//@ mechanism: `collect_sole_env_owners` identifies the `__trust_wp_tuple0()` receiver of its
//@ mechanism: call with c1 and c1's own `result == 1` grounds `driver_fn`'s ensures. The
//@ mechanism: identity-free shortcuts this front removed were what used to serve this shape.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
//@ teeth: n/a — over-refusal control; verifies on wp-s71 v2 (`driver_fn verified`, exit 0).
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
    let mut c1 = {
        #[requires(true)]
        #[ensures(result == 1)]
        |_x: i32| -> i32 { 1 }
    };
    call_plain(&mut c1, 0)
}

pub fn main() {
    assert_eq!(driver_fn(), 1);
}
