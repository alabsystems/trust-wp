//@ expect: verify
//@ xfail: the solver reaches UNSAT on the floating-point query, and strict certification withholds it: ay's
//@ xfail: proof checker has no rule for a floating-point theory lemma. D-215 names this price.
//@ mechanism: `!(x < x)` holds for every float, NaN included, under IEEE-754; unlike the controls that fold
//@ mechanism: constants, deciding it needs the floating-point theory itself.
//@ accept-means: n/a (control) — `x < x` is `false` for every float.
//@ fixed-by: n/a (control)
//@ teeth: verified on the commit before D-215 (the reals prove it too); withheld after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result)]
pub fn lt_irreflexive(x: f64) -> bool {
    !(x < x)
}
