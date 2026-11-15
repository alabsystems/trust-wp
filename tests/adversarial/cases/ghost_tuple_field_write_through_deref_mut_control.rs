//@ expect: verify
//@ xfail: a field write inside `ghost!` to a ghost tuple (`p.0 = 4` through `DerefMut::deref_mut`)
//@ xfail: flows back to `p` as the final value of the constant the tuple was built from, and the
//@ xfail: final-collapse guard's constant-carrier arm refuses it (D-14's Fix A):
//@ xfail: `error: unsupported formula: final-collapse refused (fail-closed): ^Int(2) applies a
//@ xfail: prophecy to a constant carrier`. This is the price the merge that deleted K1's
//@ xfail: `deref_mut` forwarding quarantine named (compat row ghost/assert_in_ghost.rs): the
//@ xfail: assertion had verified on the stale entry value. Retire this directive when a borrow of a
//@ xfail: constant-initialized ghost local gets a prophecy carrier at `deref_mut`.
//@ mechanism: control — the driver's ghost_tuple_mutation_post_state_verify fixture, as a case.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn ghost_tuple_field_write() {
    let mut p = ghost! {(2_i32, 3_i32)};

    let _ = ghost! {
        p.0 = 4;
    };

    let _ = ghost! {
        proof_assert!(p.0 == 4_i32);
        proof_assert!(p.1 == 3_i32);
    };
}
