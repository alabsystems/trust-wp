//@ expect: reject
//@ mechanism: match die() {} on an uninhabited-return panicking call was assumed away
//@ accept-means: f(0) panics in die(). FALSE.
//@ fixed-by: wp-s40 diverging-callees-v2
//@ teeth: verified on 8147c10d (s40 review probe q23)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum Void {}
pub fn die() -> Void { panic!() }
#[ensures(result == 1u32)]
pub fn f(x: u32) -> u32 { match x { 0 => match die() {}, _ => 1 } }
