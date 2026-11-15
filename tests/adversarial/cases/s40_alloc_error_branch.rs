//@ expect: reject
//@ timeout: 400
//@ mechanism: alloc::alloc::handle_alloc_error lives in the alloc crate, outside the core|std panic-entry filter, so the arm was assumed unreachable
//@ accept-means: a reachable handle_alloc_error was assumed unreachable. FALSE: f(0, l) aborts.
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: verified on e03182e2 (s29 review / s40 probe logs)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(x: i32, l: std::alloc::Layout) { if x <= 0 { std::alloc::handle_alloc_error(l) } }
