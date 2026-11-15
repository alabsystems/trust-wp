//@ expect: reject
//@ mechanism: wp-s41 v2 — the invariant loop call-obligation lane and the post-loop continuation name a
//@ mechanism: parameter by its entry name; the r17 guard matched only whole-local assignments.
//@ accept-means: `need_zero(p.0)` discharged from the entry value although `p.0 = 5` ran (v07)
//@ fixed-by: wp-s41 v2 extraction.rs::loop_assigns_by_value_parameter projections
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

#[requires(p.0@ == 0)]
pub fn f(mut p: (i32, i32)) {
    let mut i = 0;
    #[invariant(true)]
    while i < 2 {
        need_zero(p.0);
        p.0 = 5;
        i += 1;
    }
}
