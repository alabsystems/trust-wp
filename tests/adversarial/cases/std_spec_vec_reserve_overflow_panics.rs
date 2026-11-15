//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ mechanism: `Vec::reserve` panics with "capacity overflow" when the capacity it must grow to
//@ mechanism: exceeds `isize::MAX` bytes, and its std spec stated no precondition, so a body that
//@ mechanism: reserves an admitted element count past that size was trusted not to panic. The spec
//@ mechanism: now owes the growth bound, sized by the element type the call instantiates.
//@ accept-means: `Vec::reserve`'s spec stopped owing its capacity-overflow panic.
//@ fixed-by: D-121 — allocation-sizing std specs owe the byte bound they panic on.
//@ WHY THE CONTRACT IS FALSE: `g` claims to return normally for every `n@ >= 2^60`. The vector is
//@ WHY THE CONTRACT IS FALSE: empty, so `reserve` must grow to at least `n` `u64`s, at least `2^63`
//@ WHY THE CONTRACT IS FALSE: bytes, and `RawVec` panics with "capacity overflow" before it allocates.
//@ teeth: MEASURED as ACCEPTED, exit 0, `g verified ✓`, with the std spec tables reverted to the
//@ teeth: base; its twin std_spec_vec_reserve_in_range_control differs in the `requires` bound alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ >= 1152921504606846976)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    let mut v: Vec<u64> = Vec::new();
    v.reserve(n);
    v.len()
}
