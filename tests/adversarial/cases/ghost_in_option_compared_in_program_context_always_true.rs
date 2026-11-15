//@ expect: reject
//@ verdict: error
//@ refused-with: a value holding a `Ghost` or `Snapshot` is compared or hashed outside ghost!(...)
//@ mechanism: `Ghost` implements `PartialEq` in trust-wp-std (Creusot's does not), and at run time
//@ mechanism: `eq` returns `true` whatever the values: a ghost carries none. The validator refused a
//@ mechanism: comparison whose operand is itself a `Ghost` or `Snapshot`, but not one whose operand
//@ mechanism: only holds one: `Option<Ghost<i32>> == Option<Ghost<i32>>` runs std's `Option::eq`,
//@ mechanism: which calls the ghost's. The verifier reads the call through the `PartialEq` spec as the
//@ mechanism: logical equality of the two options, so `a != b` makes the result `false`.
//@ accept-means: `f(Some(ghost!(1)), Some(ghost!(2)))` meets `a != b` and returns `true`, while
//@ accept-means: `result == false` is reported verified.
//@ fixed-by: D-139 — a call whose bounds ask a type holding a ghost for `PartialEq`, `PartialOrd`,
//@ fixed-by: `Eq`, `Ord` or `Hash` is refused in program code.
//@ teeth: ACCEPTED (`f verified`, exit 0) when committed; natively the call above returns `true`.
//@ teeth: Refused at `a == b` under D-139.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a != b)]
#[ensures(result == false)]
pub fn f(a: Option<Ghost<i32>>, b: Option<Ghost<i32>>) -> bool {
    a == b
}
