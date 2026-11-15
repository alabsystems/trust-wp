//@ expect: reject
//@ verdict: unknown
//@ refused-with: std call can panic under a condition its spec cannot state
//@ mechanism: `Vec::drain` (and `VecDeque::drain`) panics when the range starts after it ends or
//@ mechanism: ends past the length. Its std spec was empty, so any drain was trusted. The range is
//@ mechanism: any `RangeBounds<usize>`, which a spec clause cannot read, so the call now refuses,
//@ mechanism: except where the call site instantiates the range type with `RangeFull`.
//@ accept-means: `Vec::drain` is trusted not to panic again.
//@ fixed-by: D-121 — a panic a std spec cannot state refuses the call.
//@ WHY THE CONTRACT IS FALSE: the vector is empty, and draining `0..5` from it panics.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, with the std spec tables reverted to the
//@ teeth: base.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f() -> usize {
    let mut v: Vec<u32> = Vec::new();
    let d = v.drain(0..5);
    drop(d);
    v.len()
}
