//@ expect: verify
//@ mechanism: control: requires o.is_some() then unwrap.
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ teeth: control - must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(o.is_some())]
pub fn f(o: Option<i32>) -> i32 { o.unwrap() }
