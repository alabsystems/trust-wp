//@ expect: verify
//@ mechanism: control: a requires-only recursive logic function whose recursive call sits in the else arm of `n == 0` owes its own precondition at `n - 1`. From `n >= 0` and `n != 0`, `n - 1 >= 0` holds only over the integers; ay proves it with an integer step strict certification refuses, so the walk states the arm's disequality as its integer restatement `n <= -1 || n >= 1` (`callee_preconditions::integer_hypothesis`), which a certificate checks.
//@ accept-means: n/a (control) — the call is inside the precondition at every `n >= 1`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(n >= 0)]
#[variant(n)]
pub fn f(n: Int) -> Int {
    if n == 0 { 0 } else { f(n - 1) }
}
