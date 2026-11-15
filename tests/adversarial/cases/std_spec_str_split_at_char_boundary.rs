//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: `str::split_at` takes a byte index and panics off a char boundary. Its std spec
//@ mechanism: required `mid@ <= self.len()` for a string of other than one char, and
//@ mechanism: `self.len()` in the contract DSL is the CHAR count, so any index up to the char count
//@ mechanism: was admitted; for one char it admitted every index up to the char's byte length. The
//@ mechanism: spec now requires a boundary the char view can name: 0, or the end of a one-char string.
//@ accept-means: `str::split_at` is again trusted at an index that is not a char boundary.
//@ fixed-by: D-121 — a std spec owes every panic of its function it can state.
//@ WHY THE CONTRACT IS FALSE: `f` admits `s == "aé"` with `mid == 2`; byte 2 is inside `é`, so
//@ WHY THE CONTRACT IS FALSE: `split_at` panics.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, with the std spec tables reverted to the
//@ teeth: base; its twin std_spec_str_split_at_zero_control differs in the `requires` alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(s@.len() >= 2)]
#[requires(mid@ <= s@.len())]
#[ensures(true)]
pub fn f(s: &str, mid: usize) -> usize {
    let (a, _b) = s.split_at(mid);
    a.len()
}
