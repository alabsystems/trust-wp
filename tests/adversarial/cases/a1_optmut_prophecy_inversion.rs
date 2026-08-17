//@ expect: reject
//@ mechanism: Final-collapse prophecy inversion on an enum-embedded `&mut` (Option<&mut T>)
//@ fixed-by: 932a7de (Fix A — sort-aware fail-closed guard on the Final-collapse routes)
//@ accept-means: `^r` was collapsed onto `*r` for a match binder over an Option payload, i.e. the
//@ accept-means: encoder asserted the false lemma "the caller cannot change what it borrows".
//@ accept-means: Every `&mut` postcondition in the corpus becomes untrustworthy.
//@
//@ THE BLIND SPOT THIS CLOSES: `grep -rln 'Option<&mut' reference/creusot/tests/should_fail/`
//@ returns nothing. The reference negative corpus has ZERO coverage of enum-embedded `&mut`,
//@ which is the exact shape of the adjudicated take_first_mut false accept.
//@
//@ WHY THE CONTRACT IS FALSE: `^r` is the value of the returned borrow at expiry — chosen by the
//@ CALLER, after this function returns. `caller()` below writes 9 through the returned borrow
//@ while `*r` was 7, so `^r == *r` is refuted by an actual execution.
//@ teeth: UNVERIFIED (honest). Method (ii): Fix A disabled in-tree (all four guard sites) and A/B'd
//@ teeth: in one build. This case still REJECTS with a counterexample either way — the direct
//@ teeth: `Some(x)` payload keeps the real `__trust_wp_mutref` carrier (CE distinguishes x_current=0
//@ teeth: from x_final=7), so the sort-blind routes never fire on it. Standing SHAPE gate for the
//@ teeth: documented blind spot, not a demonstrated defect detector.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(match result {
    Some(r) => ^r == *r,
    None => true,
})]
pub fn payload_prophecy_inverted(x: &mut i32) -> Option<&mut i32> {
    *x = 7;
    Some(x)
}

// The refutation, in executable Rust: after this call `*r` is 7 and `^r` is 9.
pub fn caller() {
    let mut v = 0i32;
    if let Some(r) = payload_prophecy_inverted(&mut v) {
        *r = 9;
    }
}
