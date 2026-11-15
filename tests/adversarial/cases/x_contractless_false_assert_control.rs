//@ expect: verify
//@ mechanism: over-refusal control — the true twin of `x_contractless_false_assert`
//@ xfail: the local opaque call to `pass_through` is owed `requires(false)`, so the caller is unprovable today.
//@ teeth: n/a — over-refusal control. An XPASS here while `false_assert` is still in the crate is a WARNING: the crate would be credited with an always-panicking item in it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

fn false_assert() -> i32 {
    assert!(1 + 1 == 3);
    7
}

fn pass_through(x: i32) -> i32 {
    x
}

// TRUE: caller_ok(5) returns 5.
#[ensures(result@ == x@)]
pub fn caller_ok(x: i32) -> i32 {
    pass_through(x)
}
