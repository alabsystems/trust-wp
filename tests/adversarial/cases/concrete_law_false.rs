//@ expect: reject
//@ mechanism: isolating twin of `concrete_law_proved_control`: `x <= x - 1` holds for no `x`, so the law is refuted and never credited or left live for callers
//@ accept-means: a law was credited without its postcondition being proved
//@ verdict: error
//@ refused-with: step_down postcondition FAILED (logic postcondition)
//@ teeth: the pair differs only in `+ 1` / `- 1`; before the change both printed `law postcondition unverified (non-strict axiom exposure)`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// WRONG: x <= x - 1 is false for every x.
#[logic(law)]
#[ensures(forall<x: Int> x <= x - 1)]
pub fn step_down() {}
