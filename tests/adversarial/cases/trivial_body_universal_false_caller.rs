//@ expect: reject
//@ mechanism: the same trivial-body universal one call away — a caller assumes the callee's ensures at the call site, which is sound only because the callee itself owes and is refuted on its own claim
//@ accept-means: trust-wp proved `pick` returns 5 for every input by leaning on an unproved lemma
//@ verdict: failed
//@ fn-failed: false_lemma
//@ teeth: measured — before the fix `false_lemma assumed (axiom-only function ...)` and TEETH LOST; after it, `false_lemma FAILED ✗`. `pick`'s own claim is false, so no credit is declared for it and a `pick verified` line fails the case
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: i = 0 refutes it.
#[ensures(forall<i: u32> i == 5u32)]
pub fn false_lemma() {}

// Provable only from `false_lemma`'s claim: pick(7) == 7 != 5.
#[ensures(result == 5u32)]
pub fn pick(x: u32) -> u32 {
    false_lemma();
    x
}
