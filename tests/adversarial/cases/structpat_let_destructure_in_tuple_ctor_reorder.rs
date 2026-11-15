//@ expect: reject
//@ verdict: failed
//@ fixed-by: 0d0aaba9
//@ mechanism: a named-field pattern NESTED inside a tuple-style constructor in a `let`:
//@ mechanism: `let W(S { a: aa, b: _bb }) = w;`. The outer `W(..)` is read positionally (its
//@ mechanism: one field has no name); the positional walk then recursed into the inner pattern
//@ mechanism: and lowered it positionally too, discarding `S{a,b}`. The inner pattern is now
//@ mechanism: lowered whole, as a Match on the outer field read.
//@ accept-means: the inner binding denotes the field declared first, not the one it names.
//@ WHY THE CONTRACT IS FALSE: the precondition pins `w.0.a`; `g` returns `w.0.b`.
//@ teeth: MEASURED on the merged tip 4e4613be (TRUST_WP_HARNESS_PROFILE=debug, ay a9c919158a):
//@ teeth: ACCEPTED, exit 0 — a live false accept — while its true `_control` twin FAILED, exit 1.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }
pub struct W(pub S);

#[requires({ let W(S { a: aa, b: _bb }) = w; aa@ == 5 })]
#[ensures(result@ == 5)]
pub fn g(w: W) -> u32 { w.0.b }
