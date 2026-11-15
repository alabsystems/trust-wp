//@ expect: reject
//@ mechanism: `let mut m = opaque(); if c { m = 7 }; need7(m);` before an annotated loop that sets `m = 7` and
//@ mechanism: claims `invariant(i > 0u32 ==> m == 7u32)`. `opaque` has no contract: on the path that skips the
//@ mechanism: arm, `need7` is called with whatever it returns. The parent's depth-first entry walk bound `m` to
//@ mechanism: the arm's `7` for the call on both paths (without the loop's write it is ACCEPTED as well). With
//@ mechanism: D-243 the join symbol's definition on the arm that skips names the call's result by `m`, the name
//@ mechanism: the loop's exit premises bind to 7: the case also pins that no premise after the loop reaches the
//@ mechanism: goal before it through that name.
//@ accept-means: a callee's precondition is discharged with the value one arm gives while the path that skips
//@ accept-means: the arm gives another, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(false)` calls `need7(255)`.
//@ also-verified: opaque, need7
//@ fixed-by: D-243: the walker binds locals path by path (`call_effect_paths`); `m` at the join is a symbol
//@ fixed-by: defined arm by arm.
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn opaque() -> u32 {
    255
}

#[requires(k == 7u32)]
pub fn need7(k: u32) {}

pub fn f(c: bool) {
    let mut m = opaque();
    if c {
        m = 7;
    }
    need7(m);
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    #[invariant(i > 0u32 ==> m == 7u32)]
    while i < 3 {
        m = 7;
        i += 1;
    }
}
