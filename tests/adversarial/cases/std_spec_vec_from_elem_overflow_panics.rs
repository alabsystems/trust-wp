//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ mechanism: `vec![elem; n]` lowers to `alloc::vec::from_elem`, which allocates `n` elements up
//@ mechanism: front and panics with "capacity overflow" exactly as `Vec::with_capacity(n)` does. Its
//@ mechanism: std spec stated no precondition. It now owes `n` elements of the instantiated type in
//@ mechanism: `isize::MAX` bytes.
//@ accept-means: `from_elem`'s spec stopped owing its capacity-overflow panic.
//@ fixed-by: D-121 — allocation-sizing std specs owe the byte bound they panic on.
//@ WHY THE CONTRACT IS FALSE: `g` claims to return normally for every `n@ >= 2^60`, which is at
//@ WHY THE CONTRACT IS FALSE: least `2^63` bytes of `u64`: the allocation panics before it happens.
//@ teeth: MEASURED as ACCEPTED, exit 0, `g verified ✓`, with the std spec tables reverted to the
//@ teeth: base; its twin std_spec_vec_from_elem_in_range_control differs in the `requires` bound alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ >= 1152921504606846976)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    let v = vec![0u64; n];
    v.len()
}
