//@ expect: verify
//@ xfail: the contract-free body is now a verification target, and `cap_clause_free_verdict`
//@ xfail: then demotes its clause-free `verified` to `unknown (partial: panic paths
//@ xfail: unchecked)`. The cap counts a call to a callee with a builtin std spec as an
//@ xfail: unaccounted panic site even though the call lane charges that spec's `requires`,
//@ xfail: and it counts an `assert!` arm the switch lane has just charged. An XPASS here is
//@ xfail: the signal that the cap learned to read what the extraction lane actually charged.
//@ mechanism: control for s84_ghost_deref_mut_handback — the same program asserting the value the write actually leaves behind.
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::ops::DerefMut;

pub fn k() {
    let mut g = ghost!(5i32);
    ghost! { let r = g.deref_mut(); *r = 7; };
    proof_assert!(*g == 7i32);
}
