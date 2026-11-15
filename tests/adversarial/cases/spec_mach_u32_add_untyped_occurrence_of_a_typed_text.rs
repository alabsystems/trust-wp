//@ expect: reject
//@ mechanism: one clause text, `a + b >= a`, written twice: over `u64` on a function the
//@ mechanism: type-check vehicle reads, and over `u32` on a function returning `impl Sized`, whose
//@ mechanism: clause no vehicle reads. The operator readings are keyed by clause text, so the
//@ mechanism: untyped `u32` occurrence was read at the `u64` occurrence's type: `u64` wrapping
//@ mechanism: never wraps a sum of two `u32`, and `untyped_u32` verified. In the pinned oracle the
//@ mechanism: `u32` occurrence is `UInt32$BW$.add`, which wraps (D-135 item 3).
//@ accept-means: a clause no type check reads took the reading of a clause spelled the same that
//@ accept-means: one does, at another type.
//@ WHY THE CONTRACT IS FALSE: untyped_u32: a = u32::MAX, b = 1: the wrapping sum is 0, below a.
//@ WHY THE CONTRACT IS FALSE: typed_u64: a = u64::MAX, b = 1, likewise.
//@ refused-with: also written where no type check reads it
//@ fixed-by: D-232
//@ teeth: `untyped_u32 verified` at exit 1 while the reading was the text's typed one wherever
//@ teeth: it was written; rejected once a text written where no type check reads it keeps only
//@ teeth: what holds at any type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(a + b >= a)]
pub fn typed_u64(a: u64, b: u64) {}

#[ensures(a + b >= a)]
pub fn untyped_u32(a: u32, b: u32) -> impl Sized {
    0u8
}
