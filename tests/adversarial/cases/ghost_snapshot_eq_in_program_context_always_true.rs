//@ expect: reject
//@ verdict: error
//@ refused-with: ghost values are compared outside ghost!(...)
//@ mechanism: `Ghost` and `Snapshot` implement `PartialEq` in trust-wp-std (Creusot's do not), and at
//@ mechanism: run time `eq` returns `true` whatever the values: neither carries one. The verifier
//@ mechanism: reads a program-context `==` as the equality of the logical values.
//@ accept-means: each function returns the negation of what its contract states: `f`, `g` and `k`
//@ accept-means: return `true`, `n` returns `false`.
//@ fixed-by: D-139 — a program-context comparison of ghost values is refused.
//@ teeth: ACCEPTED (all four `verified`, exit 0) when committed; natively `==` returns `true`.
//@ teeth: Refused at each of the four under D-139.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == false)]
pub fn f() -> bool {
    let a = snapshot!(1i32);
    let b = snapshot!(2i32);
    a == b
}

#[ensures(result == false)]
pub fn g() -> bool {
    let a = ghost!(1i32);
    let b = ghost!(2i32);
    a == b
}

#[ensures(result == false)]
pub fn k() -> bool {
    let a = snapshot!(1i32);
    let b = snapshot!(2i32);
    a.eq(&b)
}

#[ensures(result)]
pub fn n() -> bool {
    let a = snapshot!(1i32);
    let b = snapshot!(2i32);
    a != b
}
