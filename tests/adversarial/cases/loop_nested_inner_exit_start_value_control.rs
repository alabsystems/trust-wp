//@ expect: verify
//@ xfail: the outer body walk havocs `j` across the inner loop (D-220) and states none of the inner
//@ xfail: loop's exit facts, so the outer invariant `j == 100u32 || j == 5u32` is not shown preserved.
//@ xfail: The program is TRUE; its refutation is withheld, and a build that refutes it is wrong.
//@ xfail-verdict: unknown
//@ mechanism: control for loop_nested_inner_exit_start_value: the store `k = 1` sits under `j == 7`,
//@ mechanism: which the value `j` starts an outer iteration with never is (100, then 5), so the outer
//@ mechanism: invariant `k == 0u32` is TRUE. It was a validated `FAILED (loop invariant)`
//@ mechanism: before D-219 and D-220: a refutation of a true program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n < 1000u32)]
pub fn f(n: u32) -> u32 {
    let mut i: u32 = 0;
    let mut j: u32 = 100;
    let mut k: u32 = 0;
    #[invariant(i <= n)]
    #[invariant(k == 0u32)]
    #[invariant(j == 100u32 || j == 5u32)]
    while i < n {
        if j == 7 { k = 1; }
        j = 0;
        #[invariant(j <= 5u32)]
        while j < 5 { j += 1; }
        i += 1;
    }
    k
}
