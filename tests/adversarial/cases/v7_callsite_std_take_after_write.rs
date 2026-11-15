//@ expect: reject
//@ mechanism: the std spec of `Option::take` (`result == old(*self)`) read at a call after a
//@ mechanism: store: the call left `old(..)` over the receiver, so the caller read it at its own
//@ mechanism: entry and learned `result == *o` of the entry value.
//@ accept-means: `take` returns the value its receiver held at the caller's entry.
//@ WHY THE CONTRACT IS FALSE: the result is `Some(3)`, and the entry `*o` is arbitrary.
//@ fixed-by: D-101
//@ teeth: MEASURED on d73d0571 (debug driver): `take_false verified`. On the D-101 tree: unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == *o)]
pub fn take_false(o: &mut Option<i32>) -> Option<i32> {
    *o = Some(3);
    o.take()
}
