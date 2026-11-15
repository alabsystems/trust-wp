//@ expect: verify
//@ mechanism: a law is proved like any logic function; it used to be exposed without a proof attempt (`law postcondition unverified (non-strict axiom exposure)`) and so never credited
//@ teeth: over-refusal control — measured `law postcondition unverified (non-strict axiom exposure)`, exit 2, before; `step_up verified ✓`, exit 0, after
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(law)]
#[ensures(forall<x: Int> x <= x + 1)]
pub fn step_up() {}
