//@ expect: verify
//@ mechanism: control for logic_fn_opaque_guard_not_a_premise: the call is inside the precondition, and the function's own premises (its written requires and the parameter ranges, not the opaque guard) prove its body goals.
//@ accept-means: n/a (control) — `f(n - 1, k)` at `n > 0` and `needs_pos(1)` are inside their preconditions.
//@ note: the recursion is guarded by `n > 0`, not `n == 0`'s else arm: from `n >= 0` and `n != 0`, `n - 1 >= 0` holds only over
//@ note: the integers, and strict certification refuses that step (logic_fn_recursive_disequality_branch_control.rs).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic(opaque)]
#[requires(n >= 0)]
#[variant(n)]
pub fn f(n: Int, k: u8) -> Int {
    if n > 0 { f(n - 1, k) } else { needs_pos(1) }
}
