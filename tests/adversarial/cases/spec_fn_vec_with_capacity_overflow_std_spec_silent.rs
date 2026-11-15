//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ mechanism: a contract-bearing body trusts the std spec of every std call it makes, and the spec
//@ mechanism: of `Vec::with_capacity` stated no precondition for its capacity-overflow panic (it
//@ mechanism: stated `result@.len() == 0` only). `g`'s `requires` admits only capacities whose byte
//@ mechanism: size exceeds `isize::MAX`, so every call it admits panics, and `g` was `verified`.
//@ mechanism: The D-104 reject cases (closure_spec_call_unchecked_std_call_credited,
//@ mechanism: local_spec_callee_unchecked_std_call_credited and their siblings) left their callee's
//@ mechanism: credit undeclared on this same spec.
//@ accept-means: a std spec that omits a panic precondition lets a contract-bearing body that
//@ accept-means: panics on every admitted input verify.
//@ fixed-by: D-121 — `with_capacity` owes `capacity@ * size_of::<T>() <= isize::MAX@`, the size read
//@ fixed-by: at the call site from the element type it instantiates. s43v2_div_euclid_min_neg1 is the
//@ fixed-by: precedent: the same shape for `div_euclid`'s MIN / -1 overflow.
//@ WHY THE CONTRACT IS FALSE: `g` claims to return normally for every `n@ >= 2^60`. For `u64`
//@ WHY THE CONTRACT IS FALSE: elements that is more than `isize::MAX` bytes, and `RawVec` panics
//@ WHY THE CONTRACT IS FALSE: with "capacity overflow" before it allocates, in every build profile.
//@ teeth: MEASURED as ACCEPTED, exit 0, `g verified ✓`, with the std spec tables reverted to the
//@ teeth: base; with D-121 `g FAILED` on `(n@ * 8) <= isize::MAX@`. Its twin
//@ teeth: spec_fn_vec_with_capacity_small_control differs in the `requires` bound alone and
//@ teeth: verifies, so the rejection is the admitted inputs, not a refusal of `with_capacity`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ >= 1152921504606846976)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    Vec::<u64>::with_capacity(n).capacity()
}
