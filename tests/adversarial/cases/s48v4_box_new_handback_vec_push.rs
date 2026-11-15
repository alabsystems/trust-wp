//@ expect: reject
//@ mechanism: the `std::boxed::Box::new` allowlist entry again, reached in place through `(**b)` instead of by moving the reborrow out — a `Vec` method call through the boxed `&mut`.
//@ fixed-by: wp-s48 v4 (allowlist audit: `Box::new` deleted under the corrected reachability criterion)
//@ accept-means: `Box::new(&mut v)` freezes the Vec at its entry value, so a `push` through the boxed `&mut Vec<i32>` leaves its length unchanged as far as every later obligation is concerned.
//@ WHY THE PROGRAM IS WRONG: `(**b).push(1)` appends to `v`, so `v@.len()` is `n@ + 1` at the proof_assert; the assertion claims it is still `n@`.
//@ teeth: A/B'd on this branch: re-adding ONLY `"std::boxed::Box::new"` to
//@ teeth: FORWARDING_STD_CALLEES and rebuilding turns this case ACCEPTED (exit 0);
//@ teeth: with the audited list it is `failed` with a counterexample (exit 1). It also
//@ teeth: accepted at wp-s48 b30c81b5 and on wp-campaign
//@ teeth: (probe p2_box_vec_push, base build).
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn k() {
    let mut v: Vec<i32> = Vec::new();
    let n = v.len();
    let b = Box::new(&mut v);
    (**b).push(1);
    proof_assert!(v@.len() == n@);
}
