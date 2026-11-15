//@ expect: verify
//@ mechanism: wp-s41 v2 — a parameter the loop does not write keeps its entry name.
//@ accept-means: n/a (control) — x is only read
//@ fixed-by: wp-s41 v2 loop_merges.rs
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

#[requires(x@ == 0)]
#[ensures(result@ == 0)]
pub fn f(x: i32) -> i32 {
    let mut i = 0;
    while i < 3 {
        if x == 1 {
            break;
        }
        i += 1;
    }
    x
}
