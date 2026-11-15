//@ expect: verify
//@ mechanism: isolating twin of `fset_map_law_drops_mapping` — the true Why3 `Fset.map_def` law Creusot proves in should_succeed/cc/fset.rs
//@ xfail: `map_spec` ends `unknown (proof-trusted)`: with the membership theory and the quantified-iff split ay reaches UNSAT on both directions, and strict certification refuses the certificate
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{
    logic::{FSet, Mapping},
    prelude::*,
};

#[ensures(forall<xs: FSet<T>, f: Mapping<T, U>, y: U> xs.map(f).contains(y) == exists<x: T> xs.contains(x) && f.get(x) == y)]
pub fn map_spec<T, U>() {}
