//@ expect: verify
//@ mechanism: control: requires r.is_ok() then Result::unwrap.
//@ fixed-by: wp-s48 fixture only (Option/Result unwrap-family requires are emitted as call-site obligations)
//@ teeth: control - must keep verifying.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(r.is_ok())]
pub fn f(r: Result<i32, u8>) -> i32 { r.unwrap() }
