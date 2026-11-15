//@ expect: reject
//@ mechanism: wp-s41 v2 — the invariant loop call-obligation walk used exclusive blocks without the inner
//@ mechanism: loop's condition block and stopped at the inner header, dropping code after the inner loop (r14).
//@ accept-means: `never()` after an inner loop dropped
//@ fixed-by: wp-s41 v2 loop_body.rs inner-header continuation
//@ also-verified: need_zero, never, fine
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 0)]
fn need_zero(x: i32) {}

#[requires(false)]
fn never() {}

#[requires(true)]
fn fine(x: i32) {}

fn set5(x: &mut i32) {
    *x = 5;
}

#[requires(true)]
pub fn f() {
    let mut i = 0;
    #[invariant(true)]
    while i < 2 {
        let mut j = 0;
        #[invariant(true)]
        while j < 2 {
            j += 1;
        }
        never();
        i += 1;
    }
}
