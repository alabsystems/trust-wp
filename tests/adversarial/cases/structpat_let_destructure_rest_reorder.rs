//@ expect: reject
//@ verdict: failed
//@ fixed-by: 0d0aaba9
//@ mechanism: the `..` rest form of the `let` destructuring, `let S { a: aa, .. } = s;`. The
//@ mechanism: positional lowering read `aa` at written index 0; the rest marker was dropped with
//@ mechanism: the constructor name. The pattern now travels whole, as `S{a,..}`, to placement.
//@ accept-means: a binding denotes the field declared first, not the one it names.
//@ WHY THE CONTRACT IS FALSE: the precondition pins `a`; `g` returns `b`.
//@ teeth: MEASURED on the merged tip 4e4613be (TRUST_WP_HARNESS_PROFILE=debug, ay a9c919158a):
//@ teeth: ACCEPTED, exit 0 — a live false accept — while its true `_control` twin FAILED, exit 1.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires({ let S { a: aa, .. } = s; aa@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(s: S) -> u32 { match s { S { b, a: _a } => b } }
