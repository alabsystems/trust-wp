//@ expect: reject
//@ mechanism: a trivial-body program fn whose every ensures is a universal used to take a no-query path (ay's axiom-only classifier) and be reported `assumed`; a FALSE universal of that shape must reach the solver and be refuted
//@ accept-means: trust-wp proved that every u32 equals 5
//@ verdict: failed
//@ fn-failed: false_lemma
//@ teeth: measured — before the fix the lemma printed `false_lemma assumed (axiom-only function: 1 universal postcondition(s) with trivial body)` with no solver query and the case was TEETH LOST (verdict error, no FAILED line); after it, `false_lemma FAILED ✗ (postcondition)`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: i = 0 refutes it.
#[ensures(forall<i: u32> i == 5u32)]
pub fn false_lemma() {}
