//@ expect: verify
//@ xfail: the contract-free body is now a verification target and its body obligations are
//@ xfail: stated for the first time; ay does not decide them, so the item reports
//@ xfail: `unknown` and the run is no longer clean. The case's own claim is unaffected —
//@ xfail: nothing it asserts was refuted. An XPASS here means the newly-stated obligations
//@ xfail: became decidable.
//@ mechanism: the control for fnmut_closure_ensures_prophecy.rs — VERBATIM but for the closure's
//@ mechanism: postcondition, which here states the truth (`y == 5`, what the body writes). It
//@ mechanism: verifies today, so the corpus also detects an over-refusal if the prophecy
//@ mechanism: rendering is replaced by one that reads the capture's end-of-call value.
//@ mechanism: NOTE while its twin is ACCEPTED this control carries no proof strength: the same
//@ mechanism: unconstrained prophecy carrier that lets `y == 100` verify lets `y == 5` verify.
//@ mechanism: It becomes a real gate the moment the twin starts rejecting.
//@ accept-means: n/a — control.
//@ teeth: n/a — control; it verifies today (`driver verified`, `driver::{closure#2} verified`,
//@ teeth: exit 0).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(true)]
#[ensures(true)]
pub fn driver() -> i32 {
    let mut y: i32 = 13;
    let mut c = #[requires(true)]
    #[ensures(y == 5)]
    || {
        y = 5;
    };
    c();
    y
}

pub fn main() {
    assert_eq!(driver(), 5);
}
