//@ expect: reject
//@ verdict: failed
//@ fn-failed: diverging
//@ also-verified-assertion: creusot_test::diverging
//@ mechanism: a reachable `panic!("msg")` ARM. Its message lowers through a call with no spec,
//@ mechanism: whose fail-closed marker sits under the arm's guard, `!flag ==> false`, beside the
//@ mechanism: arm's own unreachability goal `flag`. The two are one formula, so the marker is
//@ mechanism: not counted (D-141) and the arm's refutation is published.
//@ accept-means: a body that panics on a reachable path is credited; with the marker counted it
//@ accept-means: is not credited but its real refutation is withheld as `unknown`.
//@ WHY THE CONTRACT IS FALSE: `diverging(false)` panics, and Creusot's implicit contract of a
//@ WHY THE CONTRACT IS FALSE: program function is that it does not. The assertion is TRUE: past
//@ WHY THE CONTRACT IS FALSE: the diverging arm `y` is 1.
//@ teeth: MEASURED on one build with the pairing disabled by a local knob, and on the build
//@ teeth: before it: `diverging` is `unknown (refutation withheld: goal set carries a fail-closed
//@ teeth: false ...)` there and `FAILED` with `flag = false` here.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn diverging(flag: bool) {
    let y = if flag {
        1i32
    } else {
        panic!("flag was false");
    };
    proof_assert!(y == 1i32);
}
