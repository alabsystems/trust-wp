//@ expect: verify
//@ mechanism: logic-fn identity v2 — a singleton free logic fn called with function syntax
//@ fixed-by: s35 logic-fn identity v2 (every local logic def has a unique id; method calls bind only by receiver type)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
#[logic(open)] pub fn five(x: u32) -> Int { pearlite!{5} }
#[ensures(five(u) == 5)]
pub fn g(u: u32) {}
