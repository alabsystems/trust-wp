//@ expect: reject
//@ mechanism: a loop-written local the invariant does not describe: `s` gains 2000000000 each
//@ mechanism: iteration and overflows on the third. The arithmetic walk binds `s` to a havoc at the
//@ mechanism: header, Creusot's implicit `invariant true` for a value the loop changes, and a model
//@ mechanism: of that VC is the refutation the invariant owes. D-228 withholds only a havoc for a
//@ mechanism: local no loop writes; a rule that withheld every havoc would lose this one.
//@ accept-means: `f` computes `s` past `u32::MAX` on its third iteration, and trust-wp proved
//@ accept-means: every arithmetic operation in range.
//@ verdict: failed
//@ fn-failed: f
//@ teeth: not a false-accept gate: refuted `failed` before and after D-228; it pins the flavour
//@ teeth: against a havoc rule that over-withholds.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() -> u32 {
    let mut i = 0u32;
    let mut s = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { s = s + 2000000000u32; i += 1; }
    s
}
