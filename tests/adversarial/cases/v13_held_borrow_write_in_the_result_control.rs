//@ expect: verify
//@ xfail: the result lane does not carry a write through a borrow a tuple holds to the borrowed local:
//@ xfail: the read of `a` is stale, and the TRUE `result == 5` is refuted over the value `a` held
//@ xfail: before the write (a refutation of a true claim, never a credit). D-127 made the FALSE twin
//@ xfail: fail closed; carrying the write is open.
//@ mechanism: control for v13_held_borrow_write_lost_in_the_result: the write through a borrow a
//@ mechanism: tuple holds reaches the returned local.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 5i32)]
pub fn tuple_write_true() -> i32 {
    let mut a = 3i32;
    let t = (&mut a, 0i32);
    *t.0 = 5;
    a
}
