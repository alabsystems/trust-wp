//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ mechanism: `VecDeque::with_capacity` allocates its buffer through `RawVec` and panics with
//@ mechanism: "capacity overflow" when `capacity` elements exceed `isize::MAX` bytes. Its std spec
//@ mechanism: owes that bound with the element's byte size written as a call-site marker, which the
//@ mechanism: call rewrites from the type it instantiates `T` with: 8 here.
//@ accept-means: the element size stopped reaching `VecDeque::with_capacity`'s requirement, or the
//@ accept-means: requirement was dropped.
//@ fixed-by: D-121 — allocation-sizing std specs owe the byte bound they panic on.
//@ WHY THE CONTRACT IS FALSE: `g` admits every `n@ >= 2^60`; `2^60` `u64`s are `2^63` bytes, past
//@ WHY THE CONTRACT IS FALSE: `isize::MAX`, so the call panics before it allocates.
//@ teeth: MEASURED as ACCEPTED, exit 0, `g verified ✓`, with `VECDEQUE_WITH_CAPACITY`'s
//@ teeth: requirement removed; its twin std_spec_vecdeque_with_capacity_zst_control differs in the
//@ teeth: element type alone and verifies on both binaries.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::collections::VecDeque;

#[requires(n@ >= 1152921504606846976)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    let d: VecDeque<u64> = VecDeque::with_capacity(n);
    d.len()
}
