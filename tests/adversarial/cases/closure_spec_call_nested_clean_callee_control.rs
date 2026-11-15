//@ expect: verify
//@ mechanism: the over-refusal guard for closure_spec_call_unchecked_std_call_transitive_credited:
//@ mechanism: the same two hops — a clause-free `f` calls a spec-bearing closure whose body calls a
//@ mechanism: spec-bearing fn — but every body on the way is clean (arithmetic its own lane owes),
//@ mechanism: so the walk through both reaches no unchecked site and `f` is credited.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `inc`, `f::{closure#0}` and `f verified ✓` with D-104.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
#[ensures(result@ == x@ + 1)]
pub fn inc(x: u32) -> u32 {
    x + 1
}

pub fn f() {
    let c = #[requires(x@ < 50)]
    #[ensures(result@ == x@ + 1)]
    |x: u32| inc(x);
    let _r = c(7);
}
