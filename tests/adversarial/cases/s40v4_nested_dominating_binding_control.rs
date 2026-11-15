//@ expect: verify
//@ mechanism: control: a single dominating binding in the outer body (`let k = j`) is kept for the inner loop
//@ accept-means: n/a (control) — k == j holds throughout the inner loop; TRUE contract
//@ fixed-by: wp-s40 diverging-callees-v4
//@ teeth: n/a — over-refusal control
//@ xfail: with the stale pre-loop binding `k == 0` dropped (a false premise), nothing relates k to j inside the inner loop (no `k == j` invariant, and the loop lane names both by their symbolic values), so the true precondition `k == j` is not provable — completeness cost; before v4 it verified only through the FALSE premises `j == 0` and `k == 0` (xpass on 5becf6c8)
//@ xfail: The rejection is a FALSE REFUTATION: `f FAILED (loop call obligations)` with a validated model
//@ xfail: `k != j`, a model of a VC that left the binding `k = j` out, on a TRUE program. Pinned so a move
//@ xfail: is seen; withholding it needs the inner loop's group to name a dropped pre-loop binding, as
//@ xfail: D-228 names an unstated entry value.
//@ xfail-verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k@ == j@)]
pub fn need_eq(k: u32, j: u32) {}
#[ensures(true)]
pub fn f(n: u32) { let mut j: u32 = 0; #[invariant(j <= n)] while j < n { let k: u32 = j; let mut i: u32 = 0; #[invariant(i <= n)] while i < n { need_eq(k, j); i += 1; } j += 1; } }
