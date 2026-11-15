//@ expect: reject
//@ mechanism: twin of logic_fn_recursive_disequality_branch_control, differing in one literal of the recursive call: the integer restatement of the `else` arm's disequality (`callee_preconditions::integer_hypothesis`) is a premise of the recursive call's precondition, and it must not make a false one provable.
//@ accept-means: a recursive logic function that calls itself outside its precondition is credited `verified`.
//@ WHY IT IS FALSE: at `n == 1` the body calls `f(-1)`, and `f` requires `-1 >= 0`. The variant still decreases from a non-negative `n`, so only the precondition is false.
//@ teeth: MEASURED on the commit before D-119: nothing examined (`0 verified`, exit 2). It pins that the integer restatement refutes rather than proves.
//@ fixed-by: D-119
//@ fn-failed: creusot_test::f
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(n >= 0)]
#[variant(n)]
pub fn f(n: Int) -> Int {
    if n == 0 { 0 } else { f(n - 2) }
}
