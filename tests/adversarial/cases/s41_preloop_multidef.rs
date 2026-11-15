//@ expect: reject
//@ mechanism: wp-s41 — a loop without #[invariant]/#[variant] had no loop VC, and the primary
//@ mechanism: extractor skips loop bodies (skip_loop_or_continue) and carries pre-loop values past
//@ mechanism: the loop, so obligations reachable only through a loop header were silently dropped.
//@ mechanism: Creusot checks the body under the implicit `invariant true` (havocked loop state).
//@ accept-means: v has a different value on each path into the loop; one path violates need_zero
//@ fixed-by: wp-s41 extract/unannotated_loops.rs
//@ also-verified: never, need_zero, need_small, need_lt10
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(false)]
fn never() {}

#[requires(x@ == 0)]
fn need_zero(x: i32) {}

#[requires(x@ < 5)]
fn need_small(x: i32) {}

#[requires(x@ < 10)]
fn need_lt10(x: i32) {}

#[requires(true)]
pub fn f(b: bool) {
    let v = if b { 0 } else { 5 };
    let mut i = 0;
    while i < 2 {
        need_zero(v);
        i += 1;
    }
}
