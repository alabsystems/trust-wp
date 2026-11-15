//@ expect: verify
//@ xfail: completeness — ends `unknown`: `sort-coercion bridge in negated goal: counterexample model ranges over unconstrained coercion constants disconnected from the program state` (measured 2026-09-13 on wp-s33 @ 5de5d6be, once the fixture was spelled the way Creusot types it; the earlier reason recorded here — an arity-1 carrier write rebinding the local to a fresh symbol — was observed before the respelling)
//@ mechanism: stale by-value local after a field write — over-refusal control
//@ fixed-by: s34 functional update of by-value locals on projected writes
//@ accept-means: n/a (control) — this contract is TRUE.
//@
//@ Same shape as s34_byval_scalar_newtype with the true postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S(pub u64);

#[requires(s.0 < 100u64)]
#[ensures(result.0 == s.0 + 1u64)]
pub fn param_scalar_newtype(mut s: S) -> S {
    s.0 += 1;
    s
}
