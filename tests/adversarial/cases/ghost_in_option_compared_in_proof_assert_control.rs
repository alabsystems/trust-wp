//@ expect: verify
//@ mechanism: the TRUE twin of ghost_in_option_compared_in_program_context_always_true: the same
//@ mechanism: two options of ghosts, compared in a `proof_assert!`, where `!=` is the logical
//@ mechanism: disequality and nothing runs.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified`, exit 0, when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a != b)]
#[ensures(true)]
pub fn f(a: Option<Ghost<i32>>, b: Option<Ghost<i32>>) {
    proof_assert!(a != b);
}
