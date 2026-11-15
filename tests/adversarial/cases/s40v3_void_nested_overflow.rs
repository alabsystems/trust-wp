//@ expect: reject
//@ mechanism: a check on the path to a trusted inert spin was dropped with the arm (block_reaches_panic_call never follows the assert-failure edge)
//@ accept-means: f(255, true) overflows `x + 1` in a nested arm before the Void spin. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v3
//@ teeth: verified on 51d9d0b1 (s40 v2 review probes r18/r21/r22/r26-r29)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum Void {}
pub fn spin() -> Void { loop {} }
#[ensures(result == x)]
pub fn f(x: u8, b: bool) -> u8 { if x == 255 { if b { let _y = x + 1; } match spin() {} } x }
