//@ expect: verify
//@ mechanism: a callee postcondition on the arm of `if lim > 100 { r = big(); lim = 100 }`, read past an
//@ mechanism: annotated loop under `ensures(y@ > 100 ==> result@ >= 100)`: the premise is scoped by the
//@ mechanism: switch on a local the arm reassigns. `failed` with D-243; verifies with D-244.
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ >= 100)]
pub fn big() -> u32 { 100 }

#[ensures(y@ > 100 ==> result@ >= 100)]
pub fn go(y: u32) -> u32 {
    let mut lim = y;
    let mut r = 0u32;
    if lim > 100 { r = big(); lim = 100; }
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 { i += 1; }
    r
}
