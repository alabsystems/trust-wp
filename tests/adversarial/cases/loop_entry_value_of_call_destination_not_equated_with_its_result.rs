//@ expect: reject
//@ mechanism: `let mut m = opaque(); if c { need2(m); m = 2; }` before an annotated loop. Were the call's
//@ mechanism: result named by the destination's bare name, `need2` would owe `m == 2` over the name `m`, and
//@ mechanism: the loop-entry value D-243 states (`c ==> m == 2`) would equate the same name with the arm's
//@ mechanism: later value and discharge it.
//@ accept-means: a callee's precondition is discharged with the value a local takes after the call.
//@ WHY THE CONTRACT IS FALSE: `f(true)` calls `need2(255)`.
//@ also-verified: opaque, need2
//@ teeth: rejected before and with D-243; it pins the scope of D-243 (f): a call whose destination may change again
//@ teeth: before a loop is entered names its result by a symbol of its site
//@ teeth: (`PastLoopNames::changed_again_before_the_loops`). A draft of D-243 (e) that named it `m` and stated
//@ teeth: the loop-entry value ACCEPTED it at exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn opaque() -> u32 {
    255
}

#[requires(k == 2u32)]
pub fn need2(k: u32) {}

pub fn f(c: bool) {
    let mut m = opaque();
    if c {
        need2(m);
        m = 2;
    }
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 {
        i += 1;
    }
}
