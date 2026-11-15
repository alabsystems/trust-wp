//@ expect: reject
//@ mechanism: s26 addendum shape — a LOCAL contract-less fn whose body is `assert!(1 + 1 == 3)`; it can never succeed, so it must never be reported verified, and it must not be silently vacuous
//@ accept-means: the crate was credited while holding an item that always panics — the triage's exact warning that "on the base driver `assert!(1+1==3)` reports vacuous"
//@ fixed-by: n/a — s80 addendum FALSE-ACCEPT gate; the goal kind belongs to the panic-site lane
//@ teeth: rejected on wp-s80 base and after the s80 fix. The item-level question (is `false_assert` itself reported `verified`?) is measured separately as probe P2; this suite case gates the crate-level accept.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// Contract-less, LOCAL, and unsatisfiable: every call panics.
fn false_assert() -> i32 {
    assert!(1 + 1 == 3);
    7
}

fn pass_through(x: i32) -> i32 {
    x
}

// WRONG: caller(5) returns 5, not 3 — refutable by a concrete execution that
// never touches `false_assert`, so the claim is false rather than vacuous.
#[ensures(result@ == 3i32@)]
pub fn caller(x: i32) -> i32 {
    pass_through(x)
}
