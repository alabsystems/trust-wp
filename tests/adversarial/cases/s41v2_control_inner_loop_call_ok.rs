//@ expect: verify
//@ mechanism: wp-s41 v2 — the inner-header continuation checks calls after an inner loop.
//@ accept-means: n/a (control) — `fine` requires true
//@ fixed-by: wp-s41 v2 loop_body.rs
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
        fine(j);
        i += 1;
    }
}
