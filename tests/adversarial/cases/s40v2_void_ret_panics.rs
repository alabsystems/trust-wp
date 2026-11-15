//@ expect: reject
//@ mechanism: a call returning an uninhabited empty enum (target: None, not -> !) got the trusted-spin treatment
//@ accept-means: die() panics and f(0) reaches it. FALSE.
//@ fixed-by: wp-s40 diverging-callees-v2
//@ teeth: verified on 8147c10d (s40 review probe p01)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum Void {}
pub fn die() -> Void { panic!() }
#[ensures(true)]
pub fn f(x: i32) { if x <= 0 { die(); } }
