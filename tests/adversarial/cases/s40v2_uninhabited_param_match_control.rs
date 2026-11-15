//@ expect: verify
//@ mechanism: match on an uninhabited parameter is Rust-semantically unreachable
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees-v2
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum Void {}
#[ensures(result == 1u32)]
pub fn f(x: u32, v: Option<Void>) -> u32 { match v { Some(void) => match void {}, None => 1 } }
