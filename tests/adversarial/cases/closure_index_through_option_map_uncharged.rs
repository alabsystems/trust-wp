//@ expect: reject
//@ mechanism: a contract-free CLOSURE whose only panic site is a MIR `Assert(BoundsCheck)`,
//@ mechanism: handed to a std combinator. D-95 made a contract-free `fn` with such a site a target
//@ mechanism: but deliberately left closures out, on the premise that Creusot's `coma:extspec`
//@ mechanism: turns a contract-free closure's checks into its PRECONDITION and that every caller is
//@ mechanism: charged `precondition(args)` at the call (D-54). That premise holds only where an
//@ mechanism: obligation `f.precondition(..)` exists to be charged: a call through a user generic
//@ mechanism: `F: Fn` hop, or a direct call of the closure. `Option::map` is neither. Creusot's
//@ mechanism: extern spec requires `match self { None => true, Some(t) => f.precondition((t,)) }`;
//@ mechanism: trust-wp's builtin spec for it states only an `ensures`, so the call owes nothing.
//@ mechanism: The closure is not a target (no arithmetic, and `fn_owes_abort_or_callee_precondition`
//@ mechanism: admits `Fn`/`AssocFn` only), and the host's WP sees `f(v)` as an opaque application.
//@ mechanism: The bounds goal was stated in no run, and the CONTRACTED host was credited.
//@ accept-means: `pick` is reported `verified` although `pick(Some(0), &[], 0)` panics with "index
//@ accept-means: out of bounds" inside the closure `Option::map` calls; a bounds check moved into a
//@ accept-means: closure and handed to a std combinator is examined by nobody.
//@ fixed-by: D-118. The closure escapes into `Option::map`, a callee trust-wp does not verify, so
//@ fixed-by: it is a verification target under `requires true` (every index the combinator can pass,
//@ fixed-by: every slice its capture can hold) and `pick`'s credit rests on that verdict: the closure
//@ fixed-by: is not verified and `pick` is withdrawn. option_map_guarded_closure_index_control is
//@ fixed-by: the isolating twin and keeps verifying.
//@ teeth: ACCEPTED, exit 0, `pick verified`, on the binary before D-95, after it, and at the parent
//@ teeth: of D-118. The same index with the closure called DIRECTLY in the host is refuted on
//@ teeth: `precondition(i)`, and an `x + 1` closure handed to the same `Option::map` was refuted as
//@ teeth: its own target while `pick` kept its credit. Compiled and run as a plain program,
//@ teeth: `pick(Some(0), &[], 0)` panics with "index out of bounds".
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// FALSE as a verified program function: `j` is unconstrained and `w` may be
// empty, so the closure `Option::map` calls on `Some(j)` can panic before
// `pick` returns.
#[requires(k@ < 10)]
#[ensures(result@ == k@ + 1)]
pub fn pick(o: Option<usize>, w: &[u32], k: u32) -> u32 {
    let _ = o.map(|j| w[j]);
    k + 1
}
