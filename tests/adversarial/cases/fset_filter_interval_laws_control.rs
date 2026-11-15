//@ expect: verify
//@ mechanism: isolating twin of `fset_filter_law_drops_predicate` and `fset_interval_law_off_by_one` — the true Why3 `Fset.filter_def` and `FsetInt.interval_def` laws Creusot proves in should_succeed/cc/fset.rs
//@ teeth: over-refusal control — measured `unknown (quantifier-unhandled)` for both before the membership theory existed, `verified ✓` after it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{
    logic::{FSet, Mapping},
    prelude::*,
};

#[ensures(forall<xs: FSet<T>, f: Mapping<T, bool>, x: T> xs.filter(f).contains(x) == (xs.contains(x) && f.get(x)))]
pub fn filter_spec<T>() {}

#[ensures(forall<i, j, k> FSet::interval(i, j).contains(k) == (i <= k && k < j))]
pub fn interval_spec() {}
