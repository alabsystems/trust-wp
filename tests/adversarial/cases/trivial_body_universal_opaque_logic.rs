//@ expect: reject
//@ mechanism: a trivial-body universal over a logic fn whose own body contradicts the claim must be refuted from that body, never assumed
//@ accept-means: trust-wp proved a claim about a logic function that its own body refutes
//@ verdict: failed
//@ fn-failed: secret_shift_lemma
//@ teeth: none — measured `secret_shift_lemma FAILED ✗` both before and after the fix; kept as a shape gate beside `trivial_body_universal_false`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::Int, prelude::*};

#[logic]
pub fn secret(x: Int) -> Int {
    pearlite! { x }
}

// WRONG: secret(0) == 0, not 1.
#[ensures(forall<x: Int> secret(x) == x + 1)]
pub fn secret_shift_lemma() {}
