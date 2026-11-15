//@ expect: verify
//@ mechanism: control for logic_fn_let_assertion_refuted, differing in the literal alone: the assertion follows from the binding it names, so a goal that lost the `let` would not prove it.
//@ accept-means: n/a (control) — the assertion is the binding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result == x + 1)]
pub fn f(x: Int) -> Int {
    let y = x + 1;
    proof_assert!(y == x + 1);
    y
}
