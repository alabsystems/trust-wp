//@ expect: verify
//@ mechanism: control for loop_condition_branch_write_before_exit_divides_after.rs: the condition
//@ mechanism: branches before its exit switch, but the branch writes `m`, which nothing after the
//@ mechanism: loop reads, so a fix that resolves the exit switch behind the branch must still let
//@ mechanism: `go` verify from the invariant.
//@ accept-means: n/a (control): this program is TRUE.
//@ teeth: n/a — over-refusal control for an exit-switch fix.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k == 7u32)]
pub fn need7(k: u32) {}

pub fn go() {
    let mut n = 0u32;
    let mut i = 7u32;
    let mut m = 0u32;
    #[invariant(i == 7u32)]
    #[invariant(n <= 3u32)]
    while { if n == 3 { m = 1 } n < 3 } {
        i = 7;
        n += 1;
    }
    need7(i);
}
